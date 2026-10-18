# QuanIncapacity

[![arXiv:2607.24693v3](https://img.shields.io/badge/arXiv-2607.24693v3-b31b1b.svg)](https://arxiv.org/abs/2607.24693v3)

**Lean 4 formalization of complete observable shadowing, quantum incapacity,
and universal quantum activation.**

This repository accompanies the paper:

> Chengkai Zhu and Xin Wang, **Quantum incapacity from observable shadows** (2026).
> [Version 3, 5 October 2026](https://arxiv.org/abs/2607.24693v3) · [PDF](https://arxiv.org/pdf/2607.24693v3)

The formalization develops the statistical comparison between a channel and
its full complementary channel, proves the resulting zero-information
certificates, and constructs quantum activation using a fixed qutrit channel.
It is built on [Lean-QIT](https://github.com/QuAIR/Lean-QIT) and
[mathlib](https://github.com/leanprover-community/mathlib4).

## Formalization scope

The central channel is

$$
\Lambda(X)=\frac12X+\frac14\left(\mathrm{Tr}(X)I_3-X^{\mathsf T}\right).
$$

The repository formalizes the following mathematical results and constructions.

| Area | Formalized content |
|---|---|
| Complete observable shadowing | Unbiased reconstruction under arbitrary finite references; equivalence of complete variance comparison, complex second-moment comparison, and complete positivity of the outer defect. |
| Information and capacity | BKM comparison, relative-entropy Hessian and integration, support compression and boundary regularization, tensorization, all-block zero private/coherent information, and conditional operational zero-capacity results. |
| Qutrit separation | Actual CPTP channel and full complement, nonpositive shadow map, exact CP-defect factorization, failure of antidegradability, Choi spectra, local filtering, and conditional distillation results. |
| Quantum activation | Isometric single-excitation encoding and CPTP decoding for arbitrary finite dimension, private-to-coherent conversion, finite-block padding and tensor transport, the explicit PPT partner, and conditional activation results. |
| Supporting mathematics | General private/coherent superadditivity and regularized limits, coherent-information maximizers, operator-sector dimensions and orthogonality, variance equality conditions, and Born-law/IID sample-mean statistics. |

**Operational results use explicit external theorem contracts where required.** The
channel constructions and mathematical derivations are proved in Lean.
Operational conclusions take the following standard results as named theorem
parameters where needed:

- Quantum and private coding theorems.
- The Schmidt-rank-two distillation criterion.
- The theorem that forward classical communication does not increase quantum capacity.
- The cited four-dimensional private-capacity superactivation result.

These parameters are not global axioms. Their full types and use by each
terminal theorem are documented in
[EXTERNAL_DEPENDENCIES.md](EXTERNAL_DEPENDENCIES.md). In particular, the
explicit PPT partner's operational quantum-capacity zero is proved directly
from quantum codes, without a coding-theorem parameter.

The Lean statements specify the finite-dimensional spaces, reference systems,
channel complements, parameter ranges, and external hypotheses for each result.
Numerical decimal displays are separate from the exact mathematical proofs.

## Main results

The principal Lean entry points are listed below, within namespace
`QuanIncapacity`. Operational results retain the external parameters described above.

| Result | Lean declarations |
|---|---|
| General complete-shadowing criterion | [Shadowing.completeShadow_iff_outerDefect_cp](QuanIncapacity/Framework/HermitianDilation.lean#L151), [Shadowing.complete_relativeEntropy_order_of_shadow](QuanIncapacity/Framework/SupportCriterion.lean#L96) |
| Qutrit complete observable shadowing | [qutrit_complete_shadow](QuanIncapacity/Qutrit/CompleteShadow.lean#L39) |
| Zero private and coherent information at every blocklength | [qutrit_privateOneShot_zero](QuanIncapacity/Qutrit/ZeroCapacity.lean#L22), [qutrit_coherentInformation_zero](QuanIncapacity/Qutrit/ZeroCapacity.lean#L26) |
| Zero operational private and quantum capacities | [qutrit_privateCapacity_zero](QuanIncapacity/Qutrit/ZeroCapacity.lean#L60), [qutrit_quantumCapacity_zero](QuanIncapacity/Qutrit/ZeroCapacity.lean#L64) |
| Separation from antidegradability and two-way Choi distillation | [qutrit_not_antidegradable](QuanIncapacity/Separation/NonAntidegradable.lean#L39), [qutritChoi_twoWay_distillable](QuanIncapacity/Separation/ChoiDistillation.lean#L38) |
| Universal quantum activation | [Activation.universal_activation](QuanIncapacity/Activation/UniversalActivation.lean#L46) |
| Explicit PPT activating partner | [Helper.quantumCapacity_zero](QuanIncapacity/Activation/HelperInformation.lean#L70), [Helper.superactivation](QuanIncapacity/Activation/PPTActivation.lean#L30) |
| Quantum activation with two zero-private-capacity factors | [NonprivateActivation.exists_two_nonprivate](QuanIncapacity/Activation/NonprivateActivation.lean#L80) |

## Getting started

Install [elan](https://github.com/leanprover/elan) to obtain Lean and Lake.
The repository's toolchain and dependency manifest pin the required versions.

| Dependency | Pinned version |
|---|---|
| Lean | `v4.34.0` |
| mathlib | `v4.34.0` |
| Lean-QIT | [`15a0a5ef13e5824327e0850ea896e472366287af`](https://github.com/QuAIR/Lean-QIT/tree/15a0a5ef13e5824327e0850ea896e472366287af) |

```sh
git clone https://github.com/Chengkai-Zhu/QuanIncapacity.git
cd QuanIncapacity
lake exe cache get
lake build QuanIncapacity
```

The root module, [QuanIncapacity.lean](QuanIncapacity.lean), imports every local
library module. The source is organized into:

| Directory | Purpose |
|---|---|
| [`QuanIncapacity/Framework/`](QuanIncapacity/Framework/) | General mathematical interfaces and proofs. |
| [`QuanIncapacity/Qutrit/`](QuanIncapacity/Qutrit/) | The qutrit channel, shadow map, defect, and information-zero certificates. |
| [`QuanIncapacity/Activation/`](QuanIncapacity/Activation/) | Encodings, entropy conversion, universal activation, and the PPT partner. |
| [`QuanIncapacity/Separation/`](QuanIncapacity/Separation/) | Choi structure, non-antidegradability, distillation, and the amplitude-damping counterexample. |
| [`verify/`](verify/) | Independent terminal checks, axiom auditing, source inventories, and symbolic cross-checks. |

## Verification

### Lean checks

For the independent intended-type checks and transitive axiom audit:

```sh
lake env lean -DautoImplicit=false verify/Check.lean
```

For the complete validation workflow, including root import coverage, the
build, terminal checks, axiom auditing, and source hashes
before and after validation, use Python 3 and run:

```sh
bash verify/run_checks.sh
```

The axiom whitelist is `propext`, `Classical.choice`, and `Quot.sound`.
The audit includes all declarations originating in local modules, including
private and generated declarations. Explicit external theorem parameters are
checked separately through the terminal types.

The runner writes generated logs and source manifests to `.lake/verification/`,
which is excluded from version control. See [VERIFICATION.md](VERIFICATION.md)
for the validation procedure and the scope of each check.

### Independent symbolic checks

To reproduce the exact SymPy matrix checks in an isolated Python environment:

```sh
python3 -m venv .venv
.venv/bin/python -m pip install -r verify/requirements.txt
.venv/bin/python verify/verify_matrices.py
```

These checks cover the concrete matrices, full receiver partial transpose,
and complementary environment. They complement the Lean proofs; finite
blocklength checks do not establish arbitrary-blocklength theorems.

## Documentation

- [EXTERNAL_DEPENDENCIES.md](EXTERNAL_DEPENDENCIES.md): theorem assumptions and their use in the operational results.
- [VERIFICATION.md](VERIFICATION.md): reproducible verification commands and their mathematical scope.

## Citation

If you use this formalization, please cite the associated paper:

```bibtex
@misc{zhu2026quantumincapacity,
  title         = {Quantum incapacity from observable shadows},
  author        = {Chengkai Zhu and Xin Wang},
  year          = {2026},
  eprint        = {2607.24693},
  archivePrefix = {arXiv},
  primaryClass  = {quant-ph},
  note          = {Version 3, 5 October 2026},
  doi           = {10.48550/arXiv.2607.24693},
  url           = {https://arxiv.org/abs/2607.24693v3}
}
```

For reproducible references to the code, also record the repository commit used.

## License

The code is licensed under the [Apache License 2.0](LICENSE).
Dependencies retain their respective licenses.
