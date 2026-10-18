#!/usr/bin/env python3
"""Download and unpack the Alaska CVR exports into cvr/<election>/.

    python3 scripts/download_cvr.py [election ...]

With no arguments, it fetches every election in EXPORTS. It skips an election
whose directory already holds a CvrExport file.
"""

import hashlib
import os
import shutil
import ssl
import sys
import tempfile
import urllib.request
import zipfile

RESULTS = "https://www.elections.alaska.gov/results/"
EXPORTS = {
    "2022-special": RESULTS + "22SSPG/CVR_Export_20220908084311.zip",
    "2022-general": RESULTS + "22GENR/rcv/CVR_Export.zip",
    "2024-general": RESULTS + "24GENR/CVR_Export_20241130154411.zip",
}
CVR = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "cvr")

# elections.alaska.gov does not send its intermediate certificate. The script
# fetches it from the CA Issuers URL of the server's certificate and checks it
# against this hash.
INTERMEDIATE_URL = "http://secure.globalsign.com/cacert/gsgccr46ovtlsca2025.crt"
INTERMEDIATE_SHA256 = "d160e2de4e56cb10b66c1cb0adcb79cf93c78dcd9db30c2018220262c04063f9"


def ssl_context():
    der = urllib.request.urlopen(INTERMEDIATE_URL, timeout=30).read()
    got = hashlib.sha256(der).hexdigest()
    if got != INTERMEDIATE_SHA256:
        sys.exit(f"intermediate certificate has hash {got}, expected {INTERMEDIATE_SHA256}")
    ctx = ssl.create_default_context()
    ctx.load_verify_locations(cadata=ssl.DER_cert_to_PEM_cert(der))
    return ctx


def has_export(folder):
    return os.path.isdir(folder) and any(n.startswith("CvrExport") for n in os.listdir(folder))


def main(elections):
    unknown = [e for e in elections if e not in EXPORTS]
    if unknown:
        sys.exit(f"unknown election {', '.join(unknown)}; choose from {', '.join(EXPORTS)}")
    ctx = None
    for election in elections:
        folder = os.path.join(CVR, election)
        if has_export(folder):
            print(f"{election}: already in {folder}")
            continue
        ctx = ctx or ssl_context()
        url = EXPORTS[election]
        print(f"{election}: downloading {url}")
        req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0"})
        with tempfile.TemporaryFile() as tmp:
            with urllib.request.urlopen(req, context=ctx, timeout=120) as r:
                shutil.copyfileobj(r, tmp)
            print(f"{election}: unpacking into {folder}")
            with zipfile.ZipFile(tmp) as z:
                z.extractall(folder)


if __name__ == "__main__":
    main(sys.argv[1:] or list(EXPORTS))
