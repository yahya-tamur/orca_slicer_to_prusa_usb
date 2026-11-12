"""USB print host for OrcaSlicer: the Print button writes the file to a USB drive.

Pretends to be an OctoPrint / PrusaLink server on 127.0.0.1 so Orca's Print button uploads the sliced
G-code here. The upload is written as received to the root of a removable drive, and the drive is
ejected; a small window shows the progress. No conversion happens here: the "Export as bgcode"
slicing-pipeline step of the Orca plugin converts uploads to binary G-code before they are sent.
With that step ticked the drive gets .bgcode, unticked it gets plain .gcode. Nothing is written to
the PC's disk except a short log in %LOCALAPPDATA%\\OrcaUsbBgcode.

    pythonw usb_print_host.py [--orca-pid PID] [--port 51200]

Started by the "USB bgcode export" Orca plugin; exits when the Orca process given by --orca-pid
(or the ORCA_USB_HELPER_PID environment variable) ends. Only one instance runs at a time (the port is the lock).
"""
import argparse
import ctypes
import hashlib
import http.client
import json
import logging
import os
import queue
import re
import string
import subprocess
import sys
import threading
import time
import tkinter as tk
import urllib.parse
from ctypes import wintypes
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from tkinter import ttk

import printer_page

DEFAULT_PORT = 51200
BGCODE_MAGIC = b"GCDE"  # first bytes of a Prusa binary G-code file
PRINTING_CLOSE_DELAY = 30  # seconds "Now printing" stays before the window closes by itself
LOG_DIR = os.path.join(os.environ.get("LOCALAPPDATA", os.path.expanduser("~")), "OrcaUsbBgcode")
os.makedirs(LOG_DIR, exist_ok=True)
logging.basicConfig(filename=os.path.join(LOG_DIR, "helper.log"), level=logging.INFO,
                    format="%(asctime)s %(levelname)s %(message)s")
log = logging.getLogger("usb_print_host")

# Every text the window shows comes from dialogs.json next to this file, so it can be reworded or
# translated there. A missing or broken file leaves the keys showing as [key] (and is logged).
DIALOGS_FILE = os.path.join(os.path.dirname(os.path.abspath(__file__)), "dialogs.json")
try:
    with open(DIALOGS_FILE, encoding="utf-8") as fh:
        DIALOGS = json.load(fh)
except Exception as e:
    log.error("can't read %s: %s", DIALOGS_FILE, e)
    DIALOGS = {}


def t(key, **values):
    """The dialog text for key, its lines joined and {placeholders} filled in."""
    text = DIALOGS.get(key)
    if text is None:
        log.warning("dialogs.json has no %s", key)
        return f"[{key}]"
    if isinstance(text, list):
        text = "\n".join(text)
    try:
        return text.format(**values)
    except (KeyError, IndexError, ValueError) as e:
        log.warning("dialogs.json %s: bad placeholder %s", key, e)
        return text


def count_word(n):
    """Two, Three ... Ten (from dialogs.json); digits above that."""
    words = DIALOGS.get("count_words", [])
    return words[n] if n < len(words) else str(n)


kernel32 =ctypes.WinDLL("kernel32", use_last_error=True)
kernel32.OpenProcess.restype = wintypes.HANDLE
kernel32.OpenProcess.argtypes = (wintypes.DWORD, wintypes.BOOL, wintypes.DWORD)
kernel32.WaitForSingleObject.argtypes = (wintypes.HANDLE, wintypes.DWORD)
kernel32.GetDriveTypeW.argtypes = (wintypes.LPCWSTR,)
kernel32.GetVolumeInformationW.argtypes = (wintypes.LPCWSTR, wintypes.LPWSTR, wintypes.DWORD, ctypes.c_void_p,
                                           ctypes.c_void_p, ctypes.c_void_p, wintypes.LPWSTR, wintypes.DWORD)
DRIVE_REMOVABLE = 2
SYNCHRONIZE = 0x00100000
WAIT_TIMEOUT = 0x102
CREATE_NO_WINDOW = 0x08000000
# Querying a drive whose media was just ejected must fail quietly, not pop up "insert a disk".
kernel32.SetErrorMode(0x0001 | 0x8000)  # SEM_FAILCRITICALERRORS | SEM_NOOPENFILEERRORBOX


# ------------------------------------------------------------------ drives
def removable_drives():
    """[(letter, label)] for drives Windows reports as removable and that have media."""
    drives = []
    mask = kernel32.GetLogicalDrives()
    for i, letter in enumerate(string.ascii_uppercase):
        if not mask & (1 << i):
            continue
        root = f"{letter}:\\"
        if kernel32.GetDriveTypeW(root) != DRIVE_REMOVABLE:
            continue
        label = ctypes.create_unicode_buffer(261)
        if not kernel32.GetVolumeInformationW(root, label, 261, None, None, None, None, 0):
            continue  # card reader slot without media
        drives.append((letter, label.value))
    return drives


def drive_letter_present(letter):
    return bool(kernel32.GetLogicalDrives() & (1 << (ord(letter) - ord("A"))))


def drive_ready(letter):
    """True while the drive's volume is mounted and readable. After Windows' "safe to remove" some
    USB sticks keep their drive letter (with no volume behind it) until unplugged, so the letter
    alone can't tell that the eject finished."""
    if not drive_letter_present(letter):
        return False
    return bool(kernel32.GetVolumeInformationW(f"{letter}:\\", None, 0, None, None, None, None, 0))


def request_eject(letter):
    """Explorer's 'Eject' (safe removal). Returns at once without saying whether it worked, and a
    refused one can pop up Windows' "Problem ejecting" message. Only a fallback for silent_eject."""
    cmd = ("$d=(New-Object -ComObject Shell.Application).Namespace(17).ParseName('%s:'); "
           "if ($d) { $d.InvokeVerb('Eject') }" % letter)
    subprocess.run(["powershell", "-NoProfile", "-NonInteractive", "-Command", cmd],
                   creationflags=CREATE_NO_WINDOW, timeout=60, capture_output=True)


# Silent eject through the Plug and Play configuration manager, the call "Safely Remove Hardware"
# makes: drive letter -> disk number -> disk device -> its parent (the USB device) -> eject.
setupapi = ctypes.WinDLL("setupapi", use_last_error=True)
cfgmgr32 = ctypes.WinDLL("cfgmgr32")


class GUID(ctypes.Structure):
    _fields_ = [("Data1", wintypes.DWORD), ("Data2", wintypes.WORD), ("Data3", wintypes.WORD),
                ("Data4", ctypes.c_ubyte * 8)]


class SP_DEVICE_INTERFACE_DATA(ctypes.Structure):
    _fields_ = [("cbSize", wintypes.DWORD), ("InterfaceClassGuid", GUID), ("Flags", wintypes.DWORD),
                ("Reserved", ctypes.c_size_t)]


class SP_DEVINFO_DATA(ctypes.Structure):
    _fields_ = [("cbSize", wintypes.DWORD), ("ClassGuid", GUID), ("DevInst", wintypes.DWORD),
                ("Reserved", ctypes.c_size_t)]


class STORAGE_DEVICE_NUMBER(ctypes.Structure):
    _fields_ = [("DeviceType", wintypes.DWORD), ("DeviceNumber", wintypes.DWORD),
                ("PartitionNumber", wintypes.DWORD)]


GUID_DEVINTERFACE_DISK = GUID(0x53F56307, 0xB6BF, 0x11D0, (ctypes.c_ubyte * 8)(0x94, 0xF2, 0x00, 0xA0, 0xC9, 0x1E, 0xFB, 0x8B))
DIGCF_PRESENT, DIGCF_DEVICEINTERFACE = 0x02, 0x10
IOCTL_STORAGE_GET_DEVICE_NUMBER = 0x2D1080
INVALID_HANDLE = wintypes.HANDLE(-1).value
PNP_VETO = {0: "unknown", 1: "legacy device", 2: "pending close", 3: "an application", 4: "a service",
            5: "an open file or window", 6: "another device", 7: "a driver", 8: "illegal request",
            9: "insufficient power", 10: "not disableable", 11: "legacy driver", 12: "insufficient rights",
            13: "already removed"}

kernel32.CreateFileW.restype = wintypes.HANDLE
kernel32.CreateFileW.argtypes = (wintypes.LPCWSTR, wintypes.DWORD, wintypes.DWORD, ctypes.c_void_p,
                                 wintypes.DWORD, wintypes.DWORD, wintypes.HANDLE)
kernel32.DeviceIoControl.argtypes = (wintypes.HANDLE, wintypes.DWORD, ctypes.c_void_p, wintypes.DWORD,
                                     ctypes.c_void_p, wintypes.DWORD, ctypes.POINTER(wintypes.DWORD), ctypes.c_void_p)
kernel32.CloseHandle.argtypes = (wintypes.HANDLE,)
setupapi.SetupDiGetClassDevsW.restype = wintypes.HANDLE
setupapi.SetupDiGetClassDevsW.argtypes = (ctypes.POINTER(GUID), wintypes.LPCWSTR, wintypes.HWND, wintypes.DWORD)
setupapi.SetupDiEnumDeviceInterfaces.argtypes = (wintypes.HANDLE, ctypes.c_void_p, ctypes.POINTER(GUID),
                                                 wintypes.DWORD, ctypes.POINTER(SP_DEVICE_INTERFACE_DATA))
setupapi.SetupDiGetDeviceInterfaceDetailW.argtypes = (wintypes.HANDLE, ctypes.POINTER(SP_DEVICE_INTERFACE_DATA),
                                                      ctypes.c_void_p, wintypes.DWORD,
                                                      ctypes.POINTER(wintypes.DWORD), ctypes.POINTER(SP_DEVINFO_DATA))
setupapi.SetupDiDestroyDeviceInfoList.argtypes = (wintypes.HANDLE,)
cfgmgr32.CM_Get_Parent.argtypes = (ctypes.POINTER(wintypes.DWORD), wintypes.DWORD, wintypes.ULONG)
cfgmgr32.CM_Request_Device_EjectW.argtypes = (wintypes.DWORD, ctypes.POINTER(ctypes.c_int), wintypes.LPWSTR,
                                              wintypes.ULONG, wintypes.ULONG)


def _device_number(path):
    """(DeviceType, DeviceNumber) of a volume or disk path, or None."""
    h = kernel32.CreateFileW(path, 0, 3, None, 3, 0, None)  # no access needed; share read/write; OPEN_EXISTING
    if h == INVALID_HANDLE:
        return None
    try:
        sdn, got = STORAGE_DEVICE_NUMBER(), wintypes.DWORD()
        if not kernel32.DeviceIoControl(h, IOCTL_STORAGE_GET_DEVICE_NUMBER, None, 0, ctypes.byref(sdn),
                                        ctypes.sizeof(sdn), ctypes.byref(got), None):
            return None
        return sdn.DeviceType, sdn.DeviceNumber
    finally:
        kernel32.CloseHandle(h)


def usb_device_of(letter):
    """Device instance of the USB device holding the drive letter (the parent of its disk), or None.
    Removable drives only, so a fixed disk is never ejected."""
    if kernel32.GetDriveTypeW(f"{letter}:\\") != DRIVE_REMOVABLE:
        return None
    want = _device_number(f"\\\\.\\{letter}:")
    if want is None:
        return None
    devs = setupapi.SetupDiGetClassDevsW(ctypes.byref(GUID_DEVINTERFACE_DISK), None, None,
                                         DIGCF_PRESENT | DIGCF_DEVICEINTERFACE)
    if devs == INVALID_HANDLE:
        return None
    try:
        i = 0
        while True:
            iface = SP_DEVICE_INTERFACE_DATA(cbSize=ctypes.sizeof(SP_DEVICE_INTERFACE_DATA))
            if not setupapi.SetupDiEnumDeviceInterfaces(devs, None, ctypes.byref(GUID_DEVINTERFACE_DISK), i,
                                                        ctypes.byref(iface)):
                return None
            i += 1
            need = wintypes.DWORD()
            setupapi.SetupDiGetDeviceInterfaceDetailW(devs, ctypes.byref(iface), None, 0, ctypes.byref(need), None)
            buf = ctypes.create_string_buffer(need.value)
            # SP_DEVICE_INTERFACE_DETAIL_DATA_W: DWORD cbSize, then the path; cbSize is 8 on 64-bit.
            ctypes.c_uint32.from_buffer(buf).value = 8 if ctypes.sizeof(ctypes.c_void_p) == 8 else 6
            info = SP_DEVINFO_DATA(cbSize=ctypes.sizeof(SP_DEVINFO_DATA))
            if not setupapi.SetupDiGetDeviceInterfaceDetailW(devs, ctypes.byref(iface), buf, need,
                                                             None, ctypes.byref(info)):
                continue
            path = ctypes.wstring_at(ctypes.addressof(buf) + 4)
            if _device_number(path) == want:
                parent = wintypes.DWORD()
                if cfgmgr32.CM_Get_Parent(ctypes.byref(parent), info.DevInst, 0) != 0:
                    return None
                return parent.value
    finally:
        setupapi.SetupDiDestroyDeviceInfoList(devs)


def silent_eject(devinst):
    """Ask Windows to eject the device, without any Windows message. Returns None when accepted,
    else why it was refused (e.g. "an open file or window")."""
    veto, name = ctypes.c_int(), ctypes.create_unicode_buffer(260)
    result = cfgmgr32.CM_Request_Device_EjectW(devinst, ctypes.byref(veto), name, 260, 0)
    if result == 0:
        return None
    return PNP_VETO.get(veto.value, f"veto {veto.value}") + (f" ({name.value})" if name.value else "")


FSCTL_LOCK_VOLUME, FSCTL_DISMOUNT_VOLUME = 0x90018, 0x90020
IOCTL_STORAGE_MEDIA_REMOVAL, IOCTL_STORAGE_EJECT_MEDIA = 0x2D4804, 0x2D4808
PNP_VETO_ILLEGAL_REQUEST = "illegal request"


def media_eject(letter):
    """Eject the way Explorer does for sticks Windows doesn't treat as ejectable devices (no
    'Removable' capability, so the device-level eject is an 'illegal request'): lock the volume,
    dismount it and eject the media. Silent. Returns None when done, else why not; the lock fails
    while anything still has a file or folder on the drive open."""
    h = kernel32.CreateFileW(f"\\\\.\\{letter}:", 0x80000000 | 0x40000000, 3, None, 3, 0, None)  # read/write, share r/w
    if h == INVALID_HANDLE:
        return f"can't open the drive (error {ctypes.get_last_error()})"
    try:
        got = wintypes.DWORD()

        def ioctl(code, inbuf=None, size=0):
            return kernel32.DeviceIoControl(h, code, inbuf, size, None, 0, ctypes.byref(got), None)

        if not ioctl(FSCTL_LOCK_VOLUME):
            err = ctypes.get_last_error()
            return PNP_VETO[5] if err in (5, 32) else f"lock failed (error {err})"  # access denied / sharing violation
        if not ioctl(FSCTL_DISMOUNT_VOLUME):
            return f"dismount failed (error {ctypes.get_last_error()})"
        allow = ctypes.c_ubyte(0)  # PREVENT_MEDIA_REMOVAL { FALSE }
        ioctl(IOCTL_STORAGE_MEDIA_REMOVAL, ctypes.byref(allow), 1)
        if not ioctl(IOCTL_STORAGE_EJECT_MEDIA):
            return f"eject failed (error {ctypes.get_last_error()})"
        return None
    finally:
        kernel32.CloseHandle(h)


def eject_delay(seconds):
    """Wait before the next eject attempt: quick at first (closing the window that holds the drive
    should eject within moments), slower after 2 minutes, when something is holding it on purpose.
    Each refusal adds an entry to Windows' System event log, so this caps it at ~110 per eject."""
    return 2 if seconds < 120 else 10


def eject(letter, timeout=600, waiting=None):
    """Eject and wait until the volume is gone. Windows refuses an eject while something still has
    the drive open (an Explorer window, a file opened from it, a virus scan of the new file) and
    doesn't retry by itself, so the eject is retried (see eject_delay). waiting(seconds, reason) is
    called about once a second meanwhile; reason is why the last attempt was refused, or None while
    that isn't known. False if the volume is still there after timeout."""
    start = time.time()
    devinst = usb_device_of(letter)
    method = "device" if devinst is not None else "media"
    reason, last_reason, next_try = None, None, start
    while time.time() - start < timeout:
        if not drive_ready(letter):
            return True
        now = time.time()
        if now >= next_try:
            if method == "device":
                reason = silent_eject(devinst)
                if reason and reason.startswith(PNP_VETO_ILLEGAL_REQUEST):
                    # Windows doesn't count this stick as an ejectable device: eject its media instead.
                    log.info("%s: device can't be ejected (%s), ejecting the media instead", letter, reason)
                    method = "media"
            if method == "media":
                reason = media_eject(letter)
            if method == "explorer":  # can't report refusals and may show a message each time: rarely
                request_eject(letter)
                next_try = now + 30
            else:
                if reason and reason != last_reason:
                    log.info("%s: eject refused after %.0f s: %s", letter, now - start, reason)
                if reason and reason != PNP_VETO[5] and method == "media":
                    # Not "in use" but a real failure (e.g. no access to the drive): let Explorer try.
                    log.warning("%s: media eject failed (%s), falling back to Explorer's eject", letter, reason)
                    method, reason = "explorer", None
                    continue
                last_reason = reason
                next_try = now + eject_delay(now - start)
        if waiting:
            waiting(time.time() - start, reason)
        time.sleep(0.25)
    return not drive_ready(letter)


_EXTENSION = re.compile(r"\.[A-Za-z][A-Za-z0-9]{0,5}$")  # ".gcode", ".txt" - not the ".2mm" in "part_0.2mm"


def safe_name(name, binary):
    """The name picked in Orca's upload dialog, usable as a file name on the drive.

    Returns (name, ok): folder part dropped, characters Windows forbids replaced with "_". The
    expected extension is .bgcode for binary content and .gcode for plain G-code. Ends in it -> kept
    (ok). No extension -> it is added (ok). Any other extension is kept but ok=False: the window asks
    first, since the printer judges the content by the extension."""
    expected = ".bgcode" if binary else ".gcode"
    base = os.path.basename(name.replace("\\", "/"))
    base = re.sub(r'[<>:"/\|?*\x00-\x1f]', "_", base).strip(" .")[:200] or "print"
    m = _EXTENSION.search(base)
    if m is None:
        return base + expected, True
    return base, m.group(0).lower() == expected


def with_extension(name, extension):
    """name with its extension replaced by extension."""
    m = _EXTENSION.search(name)
    return (name[:m.start()] if m else name) + extension


def numbered_name(name, taken):
    """name with " (k)" added before its extension, k the lowest number whose result isn't in taken
    (lower-case names): "file.bgcode" -> "file (1).bgcode", "file (1).bgcode" -> "file (1) (1).bgcode"."""
    m = _EXTENSION.search(name)
    stem, ext = (name[:m.start()], m.group(0)) if m else (name, "")
    k = 1
    while f"{stem} ({k}){ext}".lower() in taken:
        k += 1
    return f"{stem} ({k}){ext}"


# ------------------------------------------------------------------ PrusaLink (network alternative)
# The printer's address is "printer" in the plugin's settings (printer_page.load_config), or else the
# preset's print_host_webui (unless that points at the printer page on this PC, see printer_page.py). The
# login comes from the Orca printer preset ("printer_preset" in the plugin's settings), as entered there
# by the user: the PrusaLink password
# in the Physical Printer dialog's "API Key / Password" field (printhost_apikey); if that's empty,
# printhost_password, which is set when the preset used the PrusaLink host type. Read when needed,
# never stored or logged here.
DEFAULT_PRINTER_PRESET = "Prusa CORE One+ Gen 2 0.4 HF"


def printer_preset_path():
    name = printer_page.load_config().get("printer_preset") or DEFAULT_PRINTER_PRESET
    return os.path.join(os.environ.get("APPDATA", ""), "OrcaSlicer", "user", "default", "machine", name + ".json")


def prusalink_settings():
    """(base_url, user, password); PRUSALINK_URL overrides the address (tests)."""
    with open(printer_preset_path(), encoding="utf-8") as f:
        preset = json.load(f)
    webui = preset.get("print_host_webui") or ""
    if "127.0.0.1" in webui or "localhost" in webui:
        webui = ""  # the Device tab shows the printer page served here, not the printer itself
    base = os.environ.get("PRUSALINK_URL") or printer_page.load_config().get("printer") or webui
    if base and "://" not in base:
        base = "http://" + base
    if not base or "127.0.0.1" in base or "localhost" in base:
        raise RuntimeError(t("error_no_address"))
    password = preset.get("printhost_apikey") or preset.get("printhost_password") or ""
    return base.rstrip("/"), preset.get("printhost_user") or "maker", password


class PrusaLink:
    """Minimal PrusaLink v1 client with HTTP digest login (realm "Printer API")."""

    def __init__(self, base, user, password):
        u = urllib.parse.urlsplit(base)
        self.host, self.port = u.hostname, u.port or 80
        self.user, self.password = user, password
        self.challenge = None
        self.nc = 0

    def _authorization(self, method, uri):
        c = self.challenge
        ha1 = hashlib.md5(f"{self.user}:{c['realm']}:{self.password}".encode()).hexdigest()
        ha2 = hashlib.md5(f"{method}:{uri}".encode()).hexdigest()
        fields = {"username": self.user, "realm": c["realm"], "nonce": c["nonce"], "uri": uri}
        if "auth" in c.get("qop", "").split(","):
            self.nc += 1
            nc, cnonce = f"{self.nc:08x}", os.urandom(8).hex()
            fields.update(qop="auth", nc=nc, cnonce=cnonce)
            response = hashlib.md5(f"{ha1}:{c['nonce']}:{nc}:{cnonce}:auth:{ha2}".encode()).hexdigest()
        else:
            response = hashlib.md5(f"{ha1}:{c['nonce']}:{ha2}".encode()).hexdigest()
        fields["response"] = response
        if c.get("opaque"):
            fields["opaque"] = c["opaque"]
        return "Digest " + ", ".join(f'{k}={v}' if k in ("qop", "nc") else f'{k}="{v}"' for k, v in fields.items())

    def _request(self, method, uri, body=b"", headers=None, progress=None, cancel=None):
        for attempt in range(3):
            conn = http.client.HTTPConnection(self.host, self.port, timeout=30)
            try:
                hdrs = dict(headers or {})
                if self.challenge:
                    hdrs["Authorization"] = self._authorization(method, uri)
                if not body:
                    conn.request(method, uri, headers=hdrs)
                else:
                    hdrs["Content-Length"] = str(len(body))
                    conn.putrequest(method, uri)
                    for k, v in hdrs.items():
                        conn.putheader(k, v)
                    conn.endheaders()
                    step = 64 * 1024
                    for off in range(0, len(body), step):
                        if cancel is not None and cancel.is_set():
                            raise RuntimeError("cancelled")
                        conn.send(body[off:off + step])
                        if progress:
                            progress(min(1.0, (off + step) / len(body)))
                resp = conn.getresponse()
                data = resp.read()
                if resp.status == 401 and attempt < 2:
                    header = resp.getheader("WWW-Authenticate", "")
                    self.challenge = dict(re.findall(r'(\w+)="?([^",]*)"?', header))
                    self.nc = 0
                    if not self.challenge.get("nonce"):
                        raise RuntimeError(t("error_login_unknown", detail=header))
                    continue  # retry with the login (upload() GETs first, so a PUT body is rarely resent)
                return resp.status, data
            finally:
                conn.close()
        return resp.status, data

    def usb_storage(self):
        """Path of the printer's writable storage (its USB stick), e.g. "/usb"."""
        status, data = self._request("GET", "/api/v1/storage")
        if status == 401:
            raise RuntimeError(t("error_login"))
        if status != 200:
            raise RuntimeError(t("error_storage_list", status=status))
        for s in json.loads(data).get("storage_list", []):
            if s.get("available", True) and not s.get("read_only", s.get("ro", False)):
                return s["path"]
        raise RuntimeError(t("error_no_storage"))

    def upload(self, name, data, progress=None, cancel=None, overwrite=False):
        """PUT the file into the printer's storage (not started). Raises FileExistsError when the
        name is taken there and overwrite is False. The Buddy firmware (lib/WUI/nhttp/gcode_upload.cpp)
        answers 409 "File already exists" for that, but only after receiving the whole file; it also
        uses 409 for "Another transfer in progress" and "File is busy" (overwriting the file being
        printed), which are reported as errors instead."""
        storage = self.usb_storage().strip("/")
        uri = f"/api/v1/files/{urllib.parse.quote(storage)}/{urllib.parse.quote(name)}"
        status, body = self._request("PUT", uri, data, {"Content-Type": "text/x.gcode",
                                                        "Overwrite": "?1" if overwrite else "?0",
                                                        "Print-After-Upload": "?0"}, progress, cancel)
        if status == 409:
            text = body.decode("latin-1", "replace")
            if "already exists" in text.lower():
                raise FileExistsError(name)
            detail = next((m for m in ("Another transfer in progress", "File is busy") if m.lower() in text.lower()),
                          text.strip()[:200] or "conflict (HTTP 409)")
            raise RuntimeError(t("error_refused", file=name, detail=detail))
        if status == 401:
            raise RuntimeError(t("error_login"))
        if status not in (200, 201, 204):
            raise RuntimeError(t("error_upload", status=status, detail=body[:200].decode("latin-1", "replace")))
        return storage

    def start_print(self, storage, name):
        """Start printing a file already in the printer's storage, as the Print button of its web
        page does: POST to the file's address, no body."""
        uri = f"/api/v1/files/{urllib.parse.quote(storage.strip('/'))}/{urllib.parse.quote(name)}"
        status, body = self._request("POST", uri, headers={"Content-Type": "application/json"})
        if status == 409:
            raise RuntimeError(t("error_printer_busy"))
        if status == 401:
            raise RuntimeError(t("error_login"))
        if status not in (200, 201, 204):
            raise RuntimeError(t("error_start", status=status, detail=body[:200].decode("latin-1", "replace")))


# ------------------------------------------------------------------ jobs
class Job:
    def __init__(self, filename, data, start_print):
        self.binary = data[:4] == BGCODE_MAGIC
        self.filename, self.name_ok = safe_name(filename, self.binary)
        self.data = data
        self.start_print = start_print
        self.target = None       # name at the destination, decided when it is written
        self.overwrite = False   # the user chose Overwrite for a name taken there
        self.written = False
        self.updated_at = None   # "15:55" when a same-name upload replaced this one's content
        self.progress = 0.0      # share written so far, while copying or sending


FILE_LINE_CHARS = 56  # a file's line in the window is kept to this length (longer names are shortened)

user32 = ctypes.WinDLL("user32", use_last_error=True)
WNDENUMPROC = ctypes.WINFUNCTYPE(wintypes.BOOL, wintypes.HWND, wintypes.LPARAM)
user32.EnumWindows.argtypes = (WNDENUMPROC, wintypes.LPARAM)
user32.GetWindowThreadProcessId.argtypes = (wintypes.HWND, ctypes.POINTER(wintypes.DWORD))
user32.IsWindowVisible.argtypes = (wintypes.HWND,)
user32.GetWindow.argtypes = (wintypes.HWND, wintypes.UINT)
user32.GetWindow.restype = wintypes.HWND
user32.GetWindowRect.argtypes = (wintypes.HWND, ctypes.POINTER(wintypes.RECT))
user32.SetWindowLongPtrW.argtypes = (wintypes.HWND, ctypes.c_int, ctypes.c_ssize_t)
user32.SetWindowLongPtrW.restype = ctypes.c_ssize_t
user32.GetWindowLongPtrW.argtypes = (wintypes.HWND, ctypes.c_int)
user32.GetWindowLongPtrW.restype = ctypes.c_ssize_t
user32.IsIconic.argtypes = (wintypes.HWND,)
GW_OWNER, GWLP_HWNDPARENT = 4, -8


def main_window_of(pid):
    """The biggest visible, unowned top-level window of process pid (Orca's main window), or None."""
    best = [None, 0]

    def visit(hwnd, _):
        owner_pid = wintypes.DWORD()
        user32.GetWindowThreadProcessId(hwnd, ctypes.byref(owner_pid))
        if owner_pid.value == pid and user32.IsWindowVisible(hwnd) and not user32.GetWindow(hwnd, GW_OWNER):
            r = wintypes.RECT()
            user32.GetWindowRect(hwnd, ctypes.byref(r))
            area = (r.right - r.left) * (r.bottom - r.top)
            if area > best[1]:
                best[:] = [hwnd, area]
        return True

    user32.EnumWindows(WNDENUMPROC(visit), 0)
    return best[0]


class Window:
    """One status window per job; driven from the Tk thread via a queue."""

    def __init__(self, root, orca_pid=None):
        self.root = root
        self.orca_pid = orca_pid
        self.top = None
        self.choice = None

    def stay_above_orca(self):
        """Make Orca's main window this window's owner: Windows then always keeps it above Orca (and
        minimizes it with Orca), without putting it above other programs. Showing it from another
        process isn't enough: Orca reactivates when its upload dialog closes and covers it."""
        if not self.orca_pid:
            return
        try:
            orca = main_window_of(self.orca_pid)
            self.top.update_idletasks()  # Tk creates the window's outer frame only when it's mapped
            hwnd = int(self.top.wm_frame(), 16)
            if orca and user32.GetWindowLongPtrW(hwnd, GWLP_HWNDPARENT) != orca:
                user32.SetWindowLongPtrW(hwnd, GWLP_HWNDPARENT, orca)
        except Exception as e:
            log.warning("couldn't put the window above Orca: %s", e)

    def center_on_orca(self):
        """Move the window to the middle of Orca's main window, so it opens on Orca's monitor."""
        if not self.orca_pid:
            return
        try:
            orca = main_window_of(self.orca_pid)
            if not orca or user32.IsIconic(orca):
                return  # minimized Orca reports an off-screen position
            o, w = wintypes.RECT(), wintypes.RECT()
            user32.GetWindowRect(orca, ctypes.byref(o))
            self.top.update_idletasks()
            user32.GetWindowRect(int(self.top.wm_frame(), 16), ctypes.byref(w))  # with the title bar
            x = o.left + (o.right - o.left - (w.right - w.left)) // 2
            y = o.top + (o.bottom - o.top - (w.bottom - w.top)) // 2
            self.top.geometry(f"+{x}+{y}")
        except Exception as e:
            log.warning("couldn't center the window on Orca: %s", e)

    def show(self, filename):
        # Centered only when it opens, so a window the user has moved stays put during the batch.
        opening = self.top is None or not self.top.winfo_exists() or self.top.state() == "withdrawn"
        if self.top is None or not self.top.winfo_exists():
            self.top = tk.Toplevel(self.root)
            self.top.title(t("window_title"))
            self.top.resizable(False, False)
            self.top.protocol("WM_DELETE_WINDOW", self.close)
            # Fixed size: every area has a fixed height so changing text or buttons never resizes it.
            # The text area fits 4 lines; files_block keeps long batches within that.
            self.top.geometry("440x210")
            frm = ttk.Frame(self.top, padding=16)
            frm.pack(fill="both", expand=True)
            self.title = ttk.Label(frm, font=("Segoe UI", 11, "bold"), width=46, anchor="w")
            self.title.pack(anchor="w")
            status_box = ttk.Frame(frm, height=64, width=408)
            status_box.pack(fill="x", pady=(8, 8))
            status_box.pack_propagate(False)
            self.status = ttk.Label(status_box, wraplength=400, justify="left", anchor="nw")
            self.status.pack(fill="both", expand=True)
            self.bar = ttk.Progressbar(frm, length=408, mode="determinate", maximum=100)
            self.busy = False
            self.bar.pack(fill="x")
            self.buttons = ttk.Frame(frm, height=34)
            self.buttons.pack(fill="x", pady=(12, 0))
            self.buttons.pack_propagate(False)
        self.title.config(text=filename if len(filename) <= 46 else filename[:43] + "...")
        if opening:
            self.center_on_orca()
        self.top.deiconify()
        self.stay_above_orca()  # every time: Orca's main window may have been recreated
        self.top.lift()
        self.top.attributes("-topmost", True)
        self.top.after(300, lambda: self.top.attributes("-topmost", False))

    def update(self, text, progress=None, busy=False):
        """progress: 0..1 for a determinate bar; busy=True animates it (left running if already busy)."""
        self.status.config(text=text)
        if busy:
            if not self.busy:
                self.bar.config(mode="indeterminate", value=0)
                self.bar.start(15)
                self.busy = True
        else:
            if self.busy:
                self.bar.stop()
                self.busy = False
            self.bar.config(mode="determinate", value=100 * (progress if progress is not None else 0))

    def set_buttons(self, specs):
        for w in self.buttons.winfo_children():
            w.destroy()
        for text, cb in specs:
            ttk.Button(self.buttons, text=text, command=cb).pack(side="right", padx=(6, 0))

    def close(self):
        if self.top is not None and self.top.winfo_exists():
            self.top.withdraw()


class Worker(threading.Thread):
    """Handles uploads in batches in the single window: every upload that arrives before the drive is
    ejected joins the current batch; all of it is written, then the drive is ejected once."""

    def __init__(self, jobs, ui, test_dir=None):
        super().__init__(daemon=True)
        self.test_dir = test_dir
        self.jobs = jobs
        self.ui = ui  # queue of callables run on the Tk thread
        self.cancel = threading.Event()
        self.via_link = threading.Event()  # "Send via PrusaLink" clicked while waiting for a drive
        self.picked = queue.Queue()
        self.batch = []  # accepted uploads (named, data attached) not yet finished

    def call(self, fn, *a, **kw):
        self.ui.put(lambda: fn(*a, **kw))

    def run(self):
        while True:
            job = self.jobs.get()
            self.batch = []
            self.cancel.clear()
            try:
                self.add(job)
                while True:
                    try:
                        self.process_batch()
                        break
                    except Exception as e:
                        # E.g. the stick pulled out while writing. Try again writes the files not yet
                        # written, waiting for a drive again if needed.
                        log.exception("batch failed")
                        if not self.try_again(t("failed", error=e)):
                            break
                        self.cancel.clear()
            except Exception as e:  # keep serving later uploads
                log.exception("batch failed")
                self.finish(t("failed", error=e), 0.0)
            finally:
                self.batch = []

    # ---- batch bookkeeping
    def title(self):
        if len(self.batch) == 1:
            return t("heading_one", file=self.batch[0].filename)
        return t("heading_many", count=count_word(len(self.batch))) if self.batch else t("window_title")

    def files_block(self, room, writing=False, plain=False):
        """The batch for {files}, one file per line, in at most `room` lines (what the dialog
        leaves free of the window's 4). writing: files not yet written show their progress,
        written ones show done. A file replaced by a newer upload (and not yet written again) shows
        when. plain: names only, for a finished batch.
        More files than room: the unfinished files with the most progress (a replaced one first
        among ties), then "N files total, M done"; plain, just "N files done."."""
        jobs = self.batch

        def render(j, name):
            if plain:
                return t("file_line", file=name)
            if writing and j.written:
                return t("file_line_done", file=name)
            text = t("file_line_progress", file=name, percent=f"{j.progress:.0%}") if writing else t("file_line", file=name)
            return text + t("file_updated_suffix", time=j.updated_at) if j.updated_at else text

        def line(j):
            name = j.target or j.filename
            text = render(j, name)
            if len(text) > FILE_LINE_CHARS:  # shorten the name in the middle (keeping its end) so the line doesn't wrap
                keep = max(8, len(name) - (len(text) - FILE_LINE_CHARS) - 1)
                text = render(j, name[:keep - keep // 3] + "…" + name[len(name) - keep // 3:])
            return text

        if len(jobs) <= room:
            return "\n".join(line(j) for j in jobs)
        if plain:
            return t("files_all_done", count=len(jobs))
        # Stable sort: otherwise ties keep upload order.
        pending = sorted((j for j in jobs if not j.written), key=lambda j: (-j.progress, j.updated_at is None))
        lines = [line(j) for j in pending[:room - 1]]
        lines.append(t("files_summary", total=len(jobs), done=len(jobs) - len(pending)))
        return "\n".join(lines)

    def add(self, job):
        """Accept one upload into the batch, asking first if its name doesn't match its content."""
        data, job.data = job.data, None
        kind = "binary G-code" if job.binary else "plain G-code (Export as bgcode is unticked)"
        log.info("received %s: %s, %d bytes", job.filename, kind, len(data))
        self.call(win.show, job.filename if not self.batch else self.title())
        if not job.name_ok:
            # The picked name's extension doesn't match the content (.bgcode for binary, .gcode
            # for plain G-code): ask before writing.
            expected = ".bgcode" if job.binary else ".gcode"
            fixed = with_extension(job.filename, expected)
            self.call(win.show, job.filename)
            self.call(win.update, t("name_mismatch", file=job.filename, ext=expected))
            self.call(win.set_buttons, [(t("button_cancel"), lambda: self.picked.put(None)),
                                        (t("button_keep_name"), lambda: self.picked.put(job.filename)),
                                        (t("button_save_as", ext=expected), lambda: self.picked.put(fixed))])
            choice = self.picked.get()
            if choice is None:
                log.info("cancelled %s (user choice)", job.filename)
                self.call(win.show, self.title())
                return
            log.info("name %s -> %s (user choice)", job.filename, choice)
            job.filename = choice
        job.data = data
        # The same name uploaded again in this batch overwrites the earlier upload, which keeps the
        # name it was given (or will be given) on the drive.
        earlier = next((j for j in self.batch if j.filename.lower() == job.filename.lower()), None)
        if earlier is not None:
            if earlier.written:
                earlier.overwrite = True  # its file is ours now; rewrite it without asking
            earlier.data, earlier.binary, earlier.written, earlier.progress = job.data, job.binary, False, 0.0
            earlier.updated_at = time.strftime("%H:%M")  # shown on its line, so the upload visibly arrived
            log.info("%s overwrites the earlier upload of the same name in this batch", job.filename)
        else:
            self.batch.append(job)
        self.call(win.show, self.title())

    def resolve_target(self, job, existing, place="drive"):
        """Pick the name job gets at its destination. existing: lower-case names already there.
        A name taken there or by another file of this batch asks: Overwrite / Save as "name (k)" /
        Cancel (drops just this file). Returns False when cancelled."""
        others = {j.target.lower(): j for j in self.batch if j is not job and j.target}
        key = job.filename.lower()
        if key not in existing and key not in others:
            job.target = job.filename
            return True
        new = numbered_name(job.filename, existing | set(others))
        text = f"name_taken_{place}" if key in existing else "name_taken_batch"  # place: drive / printer
        self.call(win.show, job.filename)
        self.call(win.update, t(text, file=job.filename, new=new))
        self.call(win.set_buttons, [(t("button_cancel"), lambda: self.picked.put("cancel")),
                                    (t("button_overwrite"), lambda: self.picked.put("overwrite")),
                                    (t("button_new_file"), lambda: self.picked.put("new"))])
        choice = self.picked.get()
        self.call(win.set_buttons, [])
        log.info("name conflict for %s: %s", job.filename, choice)
        if choice == "cancel":
            self.batch.remove(job)
            self.call(win.show, self.title())
            return False
        if choice == "overwrite":
            job.target, job.overwrite = job.filename, True
            replaced = others.get(key)
            if replaced is not None and not replaced.written:
                self.batch.remove(replaced)  # never written: the new upload simply takes its place
        else:
            job.target = new
        self.call(win.show, self.title())
        return True

    def collect(self):
        """Add uploads that arrived meanwhile; True if any did."""
        added = False
        while True:
            try:
                job = self.jobs.get_nowait()
            except queue.Empty:
                return added
            self.add(job)
            added = True

    def finish(self, text, progress=1.0):
        self.call(win.update, text, progress)
        self.call(win.set_buttons, [(t("button_close"), win.close)])

    def try_again(self, text):
        """Show an error with Close / Try again and wait; True for Try again, else the window closes."""
        self.call(win.update, text, 0.0)
        self.call(win.set_buttons, [(t("button_close"), lambda: self.picked.put(False)),
                                    (t("button_try_again"), lambda: self.picked.put(True))])
        again = self.picked.get()
        self.call(win.set_buttons, [])
        if not again:
            self.call(win.close)
        return again

    # ---- the batch
    def process_batch(self):
        self.collect()
        if not self.batch:
            self.finish(t("nothing_to_write"), 0.0)
            return

        if self.test_dir:  # same naming and writing, into a folder; no drive wait or eject
            if self.write_all(self.test_dir, self.test_dir):
                self.finish(t("test_mode_done", folder=self.test_dir, files=self.files_block(3, plain=True)))
            return

        # Wait for a removable drive, collecting further uploads into the batch meanwhile.
        self.via_link.clear()

        def show_waiting():
            # Re-sent only when the text changes: the indeterminate bar keeps animating.
            self.call(win.update, t("waiting", files=self.files_block(2)), busy=True)
            self.call(win.set_buttons, [(t("button_cancel"), self.cancel.set),
                                        (t("button_send_prusalink"), self.via_link.set)])

        drives = removable_drives()
        if not drives:
            show_waiting()
        while not drives:
            if self.cancel.wait(1.0):
                self.finish(t("usb_cancelled"), 0.0)
                return
            if self.via_link.is_set():
                self.send_prusalink()
                return
            if self.collect():
                show_waiting()
            drives = removable_drives()

        if len(drives) == 1:
            letter, label = drives[0]
        else:
            self.call(win.update, t("choose_drive"))
            self.call(win.set_buttons, [(t("button_drive", drive=f"{d}: {lbl or t('drive_unnamed')}"),
                                         lambda d=d: self.picked.put(d)) for d, lbl in drives]
                                       + [(t("button_cancel"), lambda: self.picked.put(None))])
            letter = self.picked.get()
            if letter is None:
                self.finish(t("usb_cancelled"), 0.0)
                return
            label = dict(drives).get(letter, "")
        name = f"{letter}: ({label})" if label else f"{letter}:"
        self.call(win.set_buttons, [])

        if not self.write_all(f"{letter}:\\", name):
            return

        # Eject (retrying while the drive is in use), then wait for the stick to be pulled out.
        while True:
            self.call(win.update, t("ejecting", drive=name), busy=True)
            shown = [0]

            def waiting(seconds, reason):
                # Once Windows has refused (or, with the Explorer fallback, after 10 s), say the drive
                # is in use, with a counter that ticks every second between the attempts.
                if (reason or seconds >= 10) and int(seconds) != shown[0]:
                    shown[0] = int(seconds)
                    m, s = divmod(int(seconds), 60)  # 45s, 1m, 1m 34s
                    elapsed = t("elapsed_seconds", s=s) if not m else \
                        t("elapsed_minutes_seconds", m=m, s=s) if s else t("elapsed_minutes", m=m)
                    self.call(win.update, t("eject_in_use", drive=name, elapsed=elapsed), busy=True)

            if eject(letter, waiting=waiting):
                # "Upload" and "Upload and Print" behave the same: prints are started on the printer.
                self.finish(t("usb_done", drive=name, files=self.files_block(2, plain=True)))
                log.info("ejected %s", letter)
                self.close_when_unplugged(letter)
                return
            log.warning("eject of %s still not done after the timeout", letter)
            if not self.try_again(t("eject_failed", drive=name)):
                return

    def write_all(self, root, name):
        """Write every file of the batch into root, including uploads that arrive while copying.
        Each name is checked against root as it is when that file's turn comes. False if nothing
        was left to write (every file cancelled); the window then says so."""
        while True:
            pending = [j for j in self.batch if not j.written]
            if not pending:
                if not self.collect():
                    break
                continue
            for job in pending:
                if job not in self.batch:
                    continue  # dropped by an earlier conflict prompt in this round
                if job.target is None and not self.resolve_target(job, {n.lower() for n in os.listdir(root)}):
                    continue
                self.write_file(job, root, name)
                job.written = True
                self.collect()  # after each file, so a newer upload shows up at once
        if not self.batch:
            self.finish(t("nothing_written"), 0.0)
            return False
        return True

    def write_file(self, job, root, name):
        target = os.path.join(root, job.target)
        self.call(win.show, self.title())
        data, tmp = job.data, target + ".part"
        with open(tmp, "wb") as f:
            # Each chunk is flushed to the drive before the next, so the progress is the real
            # transfer and not Windows' write cache filling up.
            step = 1 << 20
            for off in range(0, len(data), step):
                f.write(data[off:off + step])
                f.flush()
                os.fsync(f.fileno())
                job.progress = frac = min(1.0, (off + step) / len(data))
                self.call(win.update, t("copying", drive=name, files=self.files_block(3, writing=True)), frac)
        os.replace(tmp, target)
        job.data = None
        log.info("wrote %s", target)

    def send_prusalink(self, sent=None):
        """Upload the batch to the printer's own storage over the network instead of a USB drive.
        sent: the files already sent, when trying again after an error (those aren't sent again)."""
        self.cancel.clear()
        self.call(win.set_buttons, [(t("button_cancel"), self.cancel.set)])
        sent = [] if sent is None else sent
        try:
            base, user, password = prusalink_settings()
            self.call(win.update, t("connecting", address=base), busy=True)
            link = PrusaLink(base, user, password)
            storage = ""
            on_printer = set()  # lower-case names the printer reported as taken (409)
            while True:
                pending = [j for j in self.batch if not j.written]
                if not pending:
                    if not self.collect():
                        break
                    continue
                for job in pending:
                    if job not in self.batch:
                        continue  # dropped by an earlier conflict prompt in this round
                    if job.target is None and not self.resolve_target(job, on_printer, "printer"):
                        continue
                    while True:
                        def progress(f, job=job):
                            job.progress = f
                            self.call(win.update, t("sending_printer", files=self.files_block(3, writing=True)), f)
                        try:
                            storage = link.upload(job.target, job.data, progress, self.cancel, job.overwrite)
                            break
                        except FileExistsError:
                            # The printer already has this name; we couldn't know in advance.
                            on_printer.add(job.target.lower())
                            if job.target != job.filename:  # "New file" was chosen: take the next number
                                taken = on_printer | {j.target.lower() for j in self.batch if j is not job and j.target}
                                job.target = numbered_name(job.filename, taken)
                            else:
                                job.target = None
                                if not self.resolve_target(job, on_printer, "printer"):
                                    break
                    if job not in self.batch:
                        continue
                    log.info("sent %s via PrusaLink to %s storage /%s", job.target, base, storage)
                    job.data, job.written = None, True
                    if job not in sent:
                        sent.append(job)
                    self.collect()  # after each file, so a newer upload shows up at once
            if not sent:
                self.finish(t("nothing_sent"), 0.0)
                return
        except Exception as e:
            log.warning("PrusaLink upload failed after %d of %d files: %s", len(sent), len(self.batch), e)
            if str(e) == "cancelled":  # the files already sent show done
                self.finish(t("send_cancelled", files=self.files_block(3, writing=True)), 0.0)
            else:  # no room for the files next to an error of up to two lines
                # Try again: e.g. after plugging a USB stick into the printer.
                if self.try_again(t("send_failed", done=len(sent), total=len(self.batch), error=e)):
                    self.send_prusalink(sent)
            return
        name = sent[0].target  # with several files, the first one sent is offered
        if len(sent) == 1:
            text = t("printer_done_one", file=name)
        else:
            text = t("printer_done_many", count=count_word(len(sent)), file=name)
        self.call(win.update, text, 1.0)
        self.call(win.set_buttons, [
            (t("button_close"), win.close),
            (t("button_start_print"), lambda: threading.Thread(target=self.start_print, args=(link, storage, name),
                                                                daemon=True).start())])

    def start_print(self, link, storage, name):
        """Start Print button after a PrusaLink send (runs off the Tk thread)."""
        self.call(win.set_buttons, [])
        self.call(win.update, t("starting", file=name), busy=True)
        try:
            link.start_print(storage, name)
        except Exception as e:
            log.warning("starting %s via PrusaLink failed: %s", name, e)
            if self.try_again(t("start_failed", file=name, error=e)):  # e.g. the printer was still busy
                self.start_print(link, storage, name)
            return
        log.info("started %s via PrusaLink", name)
        text = t("printing", file=name)
        self.call(win.update, text, 1.0)
        self.call(win.set_buttons, [(t("button_ok"), win.close)])
        # Closes by itself after 30 s, unless a newer upload has taken the window over meanwhile.
        time.sleep(PRINTING_CLOSE_DELAY)
        self.call(lambda: win.status.cget("text") == text and win.close())

    def close_when_unplugged(self, letter, timeout=600):
        """Close the window once the ejected stick is physically removed (its drive letter goes away).
        Sticks whose letter already vanished at eject can't show that, so close after a few seconds.
        A newer upload stops the wait (the run loop then starts a new batch in the same window); so
        does the timeout (the window then stays, with Close)."""
        if not drive_letter_present(letter):
            time.sleep(4)
            if self.jobs.empty():
                self.call(win.close)
            return
        end = time.time() + timeout
        while time.time() < end:
            if not self.jobs.empty():
                return
            if not drive_letter_present(letter):
                log.info("%s: unplugged", letter)
                self.call(win.close)
                return
            time.sleep(0.5)


# ------------------------------------------------------------------ fake OctoPrint
def parse_multipart(content_type, body):
    """Yield (headers dict, content bytes) for each part of a multipart/form-data body."""
    m = re.search(r'boundary="?([^";]+)"?', content_type)
    if not m:
        return
    delim = b"--" + m.group(1).encode()
    for part in body.split(delim)[1:]:
        if part.startswith(b"--"):
            break
        head, _, content = part.partition(b"\r\n\r\n")
        headers = {}
        for line in head.decode("latin-1").split("\r\n"):
            if ":" in line:
                k, v = line.split(":", 1)
                headers[k.strip().lower()] = v.strip()
        if content.endswith(b"\r\n"):
            content = content[:-2]
        yield headers, content


class Handler(BaseHTTPRequestHandler):
    server_version = "OctoPrint"
    # HTTP/1.1 so "Expect: 100-continue" (libcurl uploads) is answered; every response sets Content-Length.
    protocol_version = "HTTP/1.1"

    def _read_body(self):
        """Request body, with or without Content-Length (libcurl may send chunked)."""
        if "chunked" in self.headers.get("Transfer-Encoding", "").lower():
            parts = []
            while True:
                size = int(self.rfile.readline().split(b";")[0].strip() or b"0", 16)
                if size == 0:
                    while self.rfile.readline() not in (b"\r\n", b"\n", b""):
                        pass  # trailers
                    break
                parts.append(self.rfile.read(size))
                self.rfile.readline()  # CRLF after each chunk
            return b"".join(parts)
        return self.rfile.read(int(self.headers.get("Content-Length", 0)))

    def log_message(self, fmt, *args):
        log.info("http " + fmt, *args)

    def _json(self, code, obj, extra_headers=()):
        body = json.dumps(obj).encode()
        self.send_response(code)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        for k, v in extra_headers:
            self.send_header(k, v)
        self.end_headers()
        self.wfile.write(body)

    def _challenge(self):
        """Digest-auth clients (Orca's PrusaLink mode) first send an unauthenticated, bodyless
        request and expect 401 + a challenge; any credentials are then accepted. Returns True when
        the challenge was sent. API-key clients (X-Api-Key) are never challenged."""
        if "Authorization" in self.headers or "X-Api-Key" in self.headers:
            return False
        self._read_body()  # drain whatever was sent so the connection stays usable
        self._json(401, {"error": "authentication required"},
                   [("WWW-Authenticate", 'Digest realm="Printer API", nonce="%x", qop="auth"' % int(time.time()))])
        return True

    def _accept(self, filename, data, start_print):
        log.info("upload %s (%d bytes, print=%s)", filename, len(data), start_print)
        jobs.put(Job(filename, data, start_print))

    def do_GET(self):
        if self.path.startswith("/api/version"):
            # "OctoPrint" satisfies both Orca's OctoPrint and PrusaLink clients; upload-by-put makes
            # the PrusaLink client use PUT /api/v1/files/<storage>/<name> with the raw file.
            self._json(200, {"api": "0.1", "server": "1.10.0", "text": "OctoPrint 1.10.0 (USB bgcode helper)",
                             "capabilities": {"upload-by-put": True}})
        elif self.path.startswith("/api/v1/storage"):
            self._json(200, {"storage_list": [{"name": "USB drive", "path": "/usb", "type": "USB",
                                               "read_only": False, "available": True,
                                               "free_space": 64 * 1024 ** 3}]})
        else:
            self._json(404, {"error": "not found"})

    def do_PUT(self):
        # PrusaLink: PUT /api/v1/files/<storage>/<path...>, body = the G-code itself.
        if self._challenge():
            return
        if not self.path.startswith("/api/v1/files/"):
            return self._json(404, {"error": "not found"})
        body = self._read_body()
        name = urllib.parse.unquote(self.path.split("?", 1)[0].rstrip("/").rsplit("/", 1)[-1])
        log.info("PUT upload request: %d bytes, Transfer-Encoding=%s", len(body), self.headers.get("Transfer-Encoding"))
        if not body:
            return self._json(400, {"error": "no file"})
        self._accept(name, body, self.headers.get("Print-After-Upload", "").strip() in ("?1", "1", "true"))
        self._json(201, {"name": safe_name(name, body[:4] == BGCODE_MAGIC)[0]})

    def do_POST(self):
        # OctoPrint (and PrusaLink legacy): multipart form to /api/files/<location>.
        if self._challenge():
            return
        if not self.path.startswith("/api/files"):
            return self._json(404, {"error": "not found"})
        body = self._read_body()
        log.info("POST upload request: %d bytes, Content-Type=%s, Transfer-Encoding=%s, Expect=%s",
                 len(body), self.headers.get("Content-Type"), self.headers.get("Transfer-Encoding"),
                 self.headers.get("Expect"))
        filename, data, start_print = None, None, False
        for headers, content in parse_multipart(self.headers.get("Content-Type", ""), body):
            disp = headers.get("content-disposition", "")
            field = re.search(r'(?:^|;)\s*name="([^"]*)"', disp)
            field = field.group(1) if field else ""
            if field == "file":
                fn = re.search(r'filename="([^"]*)"', disp)
                filename = fn.group(1) if fn else "print.gcode"
                data = content
            elif field == "print":
                start_print = content.strip().lower() == b"true"
        if self.headers.get("Print-After-Upload", "").strip() in ("?1", "1", "true"):
            start_print = True
        if data is None:
            return self._json(400, {"error": "no file"})
        self._accept(filename, data, start_print)
        self._json(201, {"done": True, "files": {"local": {"name": safe_name(filename, data[:4] == BGCODE_MAGIC)[0], "origin": "local"}}})


# ------------------------------------------------------------------ main
def watch_orca(pid, root):
    handle = kernel32.OpenProcess(SYNCHRONIZE, False, pid)
    if not handle:
        log.warning("cannot open Orca process %s; not watching", pid)
        return

    def poll():
        if kernel32.WaitForSingleObject(handle, 0) != WAIT_TIMEOUT:
            log.info("Orca (pid %s) exited; shutting down", pid)
            root.quit()
        else:
            root.after(2000, poll)
    root.after(2000, poll)


def main():
    global jobs, win
    ap = argparse.ArgumentParser()
    ap.add_argument("--orca-pid", type=int)
    ap.add_argument("--port", type=int, default=DEFAULT_PORT)
    ap.add_argument("--test-dir", help="write here instead of a USB drive and skip ejecting (testing)")
    args = ap.parse_args()
    if not args.orca_pid and os.environ.get("ORCA_USB_HELPER_PID", "").isdigit():
        args.orca_pid = int(os.environ["ORCA_USB_HELPER_PID"])  # set by the Orca plugin
    try:
        server = ThreadingHTTPServer(("127.0.0.1", args.port), Handler)
    except OSError:
        log.info("port %s busy; another helper is already running", args.port)
        return
    log.info("listening on 127.0.0.1:%s (orca pid %s)", args.port, args.orca_pid)
    threading.Thread(target=server.serve_forever, daemon=True).start()
    # The printer's PrusaLink page with the camera, for Orca's Device tab (printer_page.py).
    threading.Thread(target=printer_page.serve, args=(printer_page.DEFAULT_PORT, prusalink_settings,
                                                       printer_page.load_config()), daemon=True).start()

    root = tk.Tk()
    root.withdraw()
    win = Window(root, args.orca_pid)
    jobs = queue.Queue()
    ui = queue.Queue()
    Worker(jobs, ui, args.test_dir).start()

    def pump():
        while True:
            try:
                ui.get_nowait()()
            except queue.Empty:
                break
        root.after(50, pump)
    pump()
    if args.orca_pid:
        watch_orca(args.orca_pid, root)
    root.mainloop()
    server.shutdown()
    printer_page.stop()
    log.info("stopped")


jobs = win = None
if __name__ == "__main__":
    main()
