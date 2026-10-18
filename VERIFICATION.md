# Verification

The repository provides a reproducible Lean build, independent terminal-type
checks, a transitive axiom audit, and exact symbolic matrix checks.

## Pinned environment

The environment is fixed by `lean-toolchain`, `lakefile.toml`, and
`lake-manifest.json`:

- Lean: `v4.34.0`.
- mathlib: `v4.34.0`, commit `5ed2965256430c3649e86755f9576b54eca72435`.
- Lean-QIT: commit `15a0a5ef13e5824327e0850ea896e472366287af`.
- Symbolic verification: Python 3 and SymPy `1.14.0`.

## Lean verification

From the repository root:

```sh
lake exe cache get
lake build QuanIncapacity
lake env lean -DautoImplicit=false verify/Check.lean
```

The root module imports every local library module. `verify/Check.lean` checks
selected theorems against their intended mathematical types using actual
channels, states, and parameter conditions. It also displays the named external
interfaces used by operational capacity and distillation results.

The same file collects transitive axioms for every declaration originating in a
local module, including private and generated declarations. The only permitted
axioms are:

- `propext`
- `Classical.choice`
- `Quot.sound`

The check fails on any other transitive axiom. The theorem parameters documented
in [EXTERNAL_DEPENDENCIES.md](EXTERNAL_DEPENDENCIES.md) remain explicit hypotheses
and are not certified by this axiom whitelist.

## Combined workflow

```sh
bash verify/run_checks.sh
```

The workflow checks local import coverage, records input hashes, builds the
library, runs the terminal and axiom checks, and verifies that the inputs remain
unchanged. Generated output is written under `.lake/verification/`, an ignored
build directory. An alternative output directory may be supplied as the first
argument.

The source manifests contain relative paths and SHA-256 hashes for the local
Lean modules, fixed-version configuration, CI definition, and verification
scripts. They support comparison of the exact inputs used for a run.

Lake may reuse matching build artifacts and dependency caches. A successful
incremental build should be described as such; it does not imply that every
third-party source was rebuilt from scratch.

## Exact symbolic verification

```sh
python3 -m venv .venv
.venv/bin/python -m pip install -r verify/requirements.txt
.venv/bin/python verify/verify_matrices.py
```

The symbolic checker uses exact SymPy arithmetic for:

- The qutrit Kraus formula, trace preservation, full complement, observable
  reconstruction, adjoint preservation, and CP-defect factorization.
- Defect Kraus trace orthogonality, the normalized Choi matrix, its full
  partial-transpose spectrum, and the Schmidt-rank-two witness.
- The basis outputs used to rule out antidegradability.
- Isometric qubit encoding, CPTP decoding, matrix-unit actions, and
  single-excitation tensor actions at dimensions 1 through 4.
- The PPT helper's shield states, full receiver partial transpose, Choi marginal,
  exact six-vector spectral certificate, Kraus orientation, and both receiver
  and complete six-dimensional environment outputs.

Any failed matrix certificate exits nonzero. The decimal entropy gap is printed
for readability; its exact expression and positivity have Lean proofs.

These checks complement the Lean proof library. Testing finitely many dimensions
or blocklengths does not prove the general tensor or capacity theorems. Those
results are established by the Lean statements with their documented hypotheses.

## Continuous integration

[The CI workflow](.github/workflows/ci.yml) builds the Lean library, runs the
terminal and transitive axiom checks, and executes the exact matrix checker.
Generated verification output belongs in local build directories or CI logs,
rather than in the version-controlled source tree.
