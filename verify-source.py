#!/usr/bin/env python3
"""Check the original Lean source/configuration snapshot using only Python stdlib."""
from pathlib import Path
import hashlib
import json
import sys

root = Path(__file__).resolve().parent
manifest = json.loads((root / "verification/source-snapshot.json").read_text())
failed = []
for name, expected in sorted(manifest.items()):
    path = root / name
    if not path.is_file():
        failed.append(f"missing: {name}")
        continue
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    if actual != expected:
        failed.append(f"changed: {name}")
if failed:
    print("Recorded snapshot does not match:", *failed, sep="\n", file=sys.stderr)
    sys.exit(1)
print(f"SHA-256 source snapshot verified: {len(manifest)} files.")
