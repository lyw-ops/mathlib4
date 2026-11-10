"""Check the fixed Jacobi contribution locally or on a GitHub-hosted runner."""

from pathlib import Path
import argparse
import hashlib
import json
import os
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--fetch-cache", action="store_true")
    args = parser.parse_args()
    assets = Path(__file__).resolve().parent
    source = json.loads((assets / "source.json").read_text())
    repo = Path.cwd()
    logs = repo / ".lake/jacobi-ci-results"
    logs.mkdir(parents=True, exist_ok=True)
    env = {**os.environ, "LAKE_NO_CACHE": "true"}
    env.setdefault("LEAN_NUM_THREADS", "2")
    results = []

    def git(*args):
        return subprocess.check_output(["git", *args], text=True).strip()

    if git("rev-parse", "HEAD") != source["head"]:
        raise SystemExit("The checkout does not match the fixed Jacobi commit")
    subprocess.run(
        ["git", "merge-base", "--is-ancestor", source["upstream"], "HEAD"], check=True
    )
    modules = (assets / "modules.txt").read_text().splitlines()
    tracked = ["Mathlib.lean"] + [m.replace(".", "/") + ".lean" for m in modules]
    hashes = {f: hashlib.sha256(Path(f).read_bytes()).hexdigest() for f in tracked}

    def run(label, command):
        print(f"Running {label}", flush=True)
        with (logs / f"{label}.log").open("w") as log:
            proc = subprocess.run(command, env=env, stdout=log, stderr=subprocess.STDOUT)
        results.append({"label": label, "command": command, "exit_code": proc.returncode})
        (logs / "commands.json").write_text(json.dumps(results, indent=2) + "\n")
        print((logs / f"{label}.log").read_text(), flush=True)
        if proc.returncode:
            raise SystemExit(f"{label} failed with exit code {proc.returncode}")

    if args.fetch_cache:
        run("cache", ["lake", "exe", "cache", "get", *[
            "Mathlib.Analysis.Calculus.ContDiff.CPolynomial",
            "Mathlib.Analysis.Calculus.ContDiff.Comp",
            "Mathlib.Analysis.Calculus.Deriv.Comp",
            "Mathlib.Analysis.Calculus.Deriv.Mul",
            "Mathlib.Analysis.Matrix.Normed",
            "Mathlib.LinearAlgebra.Matrix.Adjugate",
            "Mathlib.LinearAlgebra.Matrix.Trace",
        ]])
    run("build", ["lake", "--wfail", "build", *modules])
    for filename in ["ModuleAPIClients.lean", "ModuleUseClients.lean", "Audit.lean"]:
        run(Path(filename).stem, [
            "lake", "env", "lean", "-DwarningAsError=true", str(assets / filename)
        ])
    run("environment-lint", [
        "lake", "exe", "batteries/runLinter", "--no-build",
        "--only-modules=" + str(assets / "modules.txt"), modules[-1],
    ])
    aggregator = repo / "Mathlib/JacobiCILint.lean"
    if aggregator.exists():
        raise SystemExit("The temporary style-check module already exists")
    aggregator.write_text("module\n\n" + "\n".join(
        "public import " + mod for mod in sorted(modules)
    ) + "\n")
    try:
        run("style", ["lake", "exe", "lint-style", "Mathlib.JacobiCILint"])
    finally:
        aggregator.unlink()
    run("mk-all-check", ["lake", "exe", "mk_all", "--check"])
    run("patch-check", ["git", "diff", "--check", source["upstream"], "HEAD"])
    for filename, digest in hashes.items():
        if hashlib.sha256(Path(filename).read_bytes()).hexdigest() != digest:
            raise SystemExit(f"Source changed while checking: {filename}")
    if git("status", "--porcelain", "--untracked-files=no"):
        raise SystemExit("A check changed a tracked source file")
    receipt = {
        "source": source, "source_sha256": hashes, "commands": results,
        "scope": "Jacobi modules, transitive dependencies, clients, axioms and linters",
    }
    (logs / "RECEIPT.json").write_text(json.dumps(receipt, indent=2) + "\n")
    if summary := os.environ.get("GITHUB_STEP_SUMMARY"):
        with Path(summary).open("a") as page:
            page.write(
                "## Jacobi contribution checks passed\n\n"
                f"Tested source: `{source['head']}`\n\n"
                f"Upstream base: `{source['upstream']}`\n\n"
                "Strict module build, downstream clients, all-declaration axiom audit, "
                "environment/style linters, import aggregator and patch checks passed.\n\n"
                "Scope: the two Jacobi modules and their dependencies; "
                "the complete upstream Mathlib CI runs on a formal upstream PR.\n"
            )
    print("All Jacobi contribution checks passed", flush=True)


if __name__ == "__main__":
    main()
