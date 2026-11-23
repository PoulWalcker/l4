"""Run from a checkout with Lean and Lake on PATH: python3 tests/cli.py."""

from pathlib import Path
import os
import re
import shutil
import subprocess
from tempfile import TemporaryDirectory

ROOT = Path(__file__).resolve().parents[1]
BINARY = ROOT / ".lake/build/bin/l4"


def check(project, target, exit_code, expected, error=None, summary=None):
    result = subprocess.run(
        [BINARY, target], cwd=project, capture_output=True, text=True, timeout=60
    )
    findings = []
    lines = result.stdout.splitlines()
    if summary is not None and (not lines or lines.pop() != summary):
        raise AssertionError(f"{target}: expected {summary!r} in {result.stdout}")
    for line in lines:
        match = re.fullmatch(r".*:(\d+): (No-Go|Warning) (\w+) .+", line)
        if match is None:
            raise AssertionError(f"{target}: unrecognized output: {line}")
        findings.append((int(match[1]), match[2], match[3]))
    if error is not None and error not in result.stderr:
        raise AssertionError(f"{target}: missing {error!r} in {result.stderr}")
    if result.returncode != exit_code or findings != expected:
        raise AssertionError(
            f"{target}: expected exit {exit_code} and {expected}\n"
            f"received exit {result.returncode}\n{result.stdout}{result.stderr}"
        )


def main():
    subprocess.run(["lake", "build", "l4"], cwd=ROOT, check=True)
    with TemporaryDirectory() as tmp:
        project = Path(tmp)
        shutil.copytree(ROOT / "tests/cases", project, dirs_exist_ok=True)
        shutil.copy(ROOT / "lean-toolchain", project)
        subprocess.run(["lake", "build", "+io.TestDriver"], cwd=project, check=True)
        check(project, "Clean.lean", 0, [])
        check(project, "pure/Data.lean", 0, [])
        check(project, "Behavior.lean", 0, [
            (3, "Warning", "W02"), (4, "Warning", "W03"),
            (7, "Warning", "W04"), (10, "Warning", "W16"),
            (13, "Warning", "W17"), (16, "Warning", "W19"),
            (19, "Warning", "W12"), (22, "Warning", "W13"), (25, "Warning", "W16"),
            (31, "Warning", "W19"),
        ])
        check(project, "Forbidden.lean", 1, [
            (1, "No-Go", "N02"), (2, "No-Go", "N03"), (3, "No-Go", "N04"),
            (4, "No-Go", "N05"), (5, "No-Go", "N05"),
            (6, "Warning", "W10"), (7, "Warning", "W11"), (8, "Warning", "W11"),
            (9, "No-Go", "N05"), (10, "No-Go", "N04"), (11, "No-Go", "N04"),
            (12, "No-Go", "N03"), (13, "Warning", "W11"), (14, "No-Go", "N05"),
        ])
        check(project, "pure/Dependency.lean", 1, [
            (3, "No-Go", "I02"), (5, "No-Go", "I01"),
            (6, "No-Go", "I01"), (7, "No-Go", "I01"), (8, "No-Go", "I01"),
            (9, "No-Go", "I01"),
        ])
        if os.name == "posix":
            (project / "Clock.lean").write_text("def clock := IO.monoMsNow\n")
            (project / "pure/Link.lean").symlink_to("../Clock.lean")
            check(project, "pure/Link.lean", 1, [(1, "No-Go", "I01")])
        (project / "Multiline.lean").write_text(
            'import Lean\ndef marker (j : Lean.Json) := (\n  j.compress.contains "ready"\n)\n'
        )
        check(project, "Multiline.lean", 0, [(3, "Warning", "W03")])
        check(project, "Invalid.lean", 2, [], error="Type mismatch")
        (project / "EarlyExit.lean").write_text("#exit\ndef hidden : Nat := sorry\n")
        check(project, "EarlyExit.lean", 2, [], error="#exit")

        scan = project / "scan"
        (scan / ".lake").mkdir(parents=True)
        shutil.copy(project / "Invalid.lean", scan / ".lake")
        (scan / "browser.html").write_text("<main></main>")
        (scan / "Ready.lean").write_text("def ready := true\n")
        check(project, "scan", 0, [(0, "Warning", "B03")],
              summary="Audited 1 Lean files; 0 files with No-Go; 0 analysis errors")
        shutil.copy(project / "Invalid.lean", scan)
        (scan / "Bad.lean").write_text("def tick := IO.sleep\n")
        check(project, "scan", 2, [(0, "Warning", "B03"), (1, "No-Go", "N02")],
              error="Type mismatch",
              summary="Audited 3 Lean files; 1 files with No-Go; 1 analysis errors")
        # The local Std directory shadows the toolchain's Std imports once built.
        subprocess.run(["lake", "build", "+Std.Probe"], cwd=project, check=True)
        (project / "ImportProbe.lean").write_text("import Std.Probe\ndef total := DomainProbe.get! 4\n")
        check(project, "ImportProbe.lean", 0, [])
    print("CLI regressions passed")


if __name__ == "__main__":
    main()
