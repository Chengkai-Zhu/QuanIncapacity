# External theorem assumptions

The formalization separates locally proved mathematics from standard external
results used by operational capacity and distillation theorems. External results
are explicit parameters of the relevant Lean statements. They are not global
axioms or automatically supplied typeclass instances.

## Interfaces

| External result | Lean interface | Mathematical meaning |
|---|---|---|
| Quantum coding theorem | `External.QuantumCoding N` | Lean-QIT's operational quantum capacity equals the independently defined regularized coherent information of `N`. |
| Private coding theorem | `External.PrivateCoding N M` | For a certified complementary pair, operational strong private capacity equals regularized private information. |
| Schmidt-rank-two distillation criterion | `External.SchmidtRankTwoDistillation` | A Schmidt-rank-two negative partial-transpose witness implies positive two-way distillable entanglement under the defined finite-round LOCC protocols. |
| Forward classical assistance | `External.ForwardClassicalNoIncreaseQuantumCapacity N` | Achievable quantum rates with forward classical communication do not exceed the unassisted operational quantum capacity. |
| Four-dimensional private superactivation | `External.FourDimensionalPrivateSuperactivationWitness` | An actual `4 → 4` channel with a full complementary-channel certificate has zero private capacity and positive private capacity when tensored with qubit half-erasure, as in [arXiv:2609.10520v1](https://arxiv.org/abs/2609.10520v1). |

The full interface definitions are in
[PrivateCapacity.lean](QuanIncapacity/Framework/PrivateCapacity.lean),
[Distillation.lean](QuanIncapacity/Framework/Distillation.lean),
[ForwardAssistance.lean](QuanIncapacity/Framework/ForwardAssistance.lean), and
[NonprivateActivation.lean](QuanIncapacity/Activation/NonprivateActivation.lean).

## Operational definitions

`ComplementaryChannels N M` requires that both channels are the two marginal
outputs of the same Stinespring isometry, including its entire environment.

Private codes use uniform messages, an actual encoder and POVM decoder,
average decoding error, and total Holevo leakage tending to zero. The secrecy
condition concerns total leakage rather than leakage per channel use. Quantum
capacity uses the operational definition supplied by Lean-QIT.

Entropies and information quantities are in bits. The BKM metric uses natural
logarithms; the relative-entropy Hessian includes the proved `1 / ln 2` conversion.

## Use by the main results

| Result | External parameters |
|---|---|
| `qutrit_privateCapacity_zero` | Private coding for `Λ, Λc`. |
| `qutrit_quantumCapacity_zero` | Quantum coding for `Λ`. |
| `Activation.universal_activation` | Quantum coding for the actual product `N.prod Λ`. Positive private capacity is used through its operational definition. |
| `Helper.activation` | Private coding for the helper and its full complement; quantum coding for `M_H.prod Λ`. |
| `Helper.superactivation` | The preceding parameters, plus quantum coding for `Λ` to include both factors' zero quantum capacities. |
| `qutritChoi_twoWay_distillable` | The Schmidt-rank-two distillation criterion. |
| `qutritChoi_oneWay_zero` | The forward-assistance theorem for `Λ` and quantum coding for `Λ`. |
| `qutrit_partner_private_zero` / `qutrit_partner_quantum_zero` | Respectively, private or quantum coding for the actual product channel. Complementarity and complete domination are explicit premises. |
| `NonprivateActivation.exists_two_nonprivate` | The four-dimensional external witness, private coding for the constructed second factor, and quantum coding for the final product. |
| `AmplitudeDamping.quantumCapacity_pos` | Quantum coding for the amplitude-damping channel. |

## Locally proved mathematics

The complete-shadowing criterion, CP-defect equivalence, BKM comparison,
relative-entropy integration and boundary regularization, output-support
compression, tensorization, and all-block zero-information statements are
proved locally. The same holds for general information superadditivity,
regularized limits, and attainment of the coherent-information maximum.

The activation construction proves the actual encoders, decoders, full
complements, entropy branch identities, and finite positive-information block.
The private-to-coherent bound is

$$
I_{\mathrm c}\ge q\eta a-qh_2(\eta)-(1-q)b.
$$

A finite block is selected first, followed by padding to `L = max(n,d)` and
physical tensor transport. No assumption on auxiliary-dimension growth is used.

The PPT fidelity bound and `Helper.quantumCapacity_zero` are proved directly
from operational quantum codes, without a quantum coding theorem parameter.
The helper's exact private-information expression, full environment equality,
and strict positive gap are also locally proved.

[Check.lean](verify/Check.lean) checks terminal statements and displays the
external interfaces. Its transitive axiom audit is a separate check: a clean
axiom list does not establish the truth of a supplied external theorem parameter.
