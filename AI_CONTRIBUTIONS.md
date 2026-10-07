# AI contribution and verification statement

**Prepared and curated by Xin Shen**  
**AI-generated candidate proof — v0.1, 7 October 2026**

## Generation and contributions

This note was developed in OpenAI Codex on 7 October 2026. The assistant
was identified in the session as belonging to the GPT-6 family. The exact
deployed model identifier and any distinct sub-agent model identifiers
were not recorded in the publication materials and are not asserted here.
The workflow used AI agents, local Python computations, and LaTeX
compilation. The released verifier uses the Python standard library;
its decisions use exact fractions and outward-rounded integer intervals.

AI agents contributed to the core proof development: adapting the
Fock-space strategy, deriving the bosonic operator and comparison bounds,
constructing the finite certificates, writing the verification programs,
optimizing the stated threshold, and drafting and editing the manuscript.
AI agents also performed the internal mathematical and computational
cross-checks recorded in this repository. AI involvement was not limited
to language editing or routine computation.

Xin Shen supplied the research question and source paper, directed the
bosonic extension and subsequent checks and threshold optimization,
set the editorial and disclosure requirements, curated the output, and
authorized this candidate-proof release. No separate line-by-line human
verification of the proof is recorded or claimed in v0.1.

## Methodological source

The immediate source is OpenAI,
[*A Fock-space inequality and the Laughlin spectral gap*](https://github.com/openai/math/blob/main/preprints/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026/A-Fock-space-inequality-and-the-Laughlin-spectral-gap-September-24-2026.pdf),
dated 24 September 2026. Its full-Fock-space comparison strategy is
adapted here to a different particle statistics and pseudopotential.
The Introduction and in-text citations identify this dependence and
credit the relevant human-authored literature. The present note does
not report an independent audit of every claim in that source preprint.

## Recorded checks

The complete arithmetic replay passed in the preparation workflow:

1. Exact planar positivity and kernel checks in all 26 retained blocks.
2. Rational negative-tail bounds and the scalar coherent-comparison budgets.
3. The 26 retained blocks in each of six flux ranges, totaling 156
   interval block certificates, with exact combination of the final budgets.

The ranges are $[3088,3090]$, $[3090,3100]$, $[3100,3125]$,
$[3125,3300]$, $[3300,4000]$, and $[4000,\infty)$.
The scripts and recorded outputs are supplied for reproduction. Their
success flags certify the implemented arithmetic checks. The driver
does not automatically verify all analytic operator identities in the
manuscript or compare every release file against its manifest.

Internal AI cross-checks examined the finite kernels, four-body coherent
comparison, sphere transfer, and interval implementation. Records whose
filenames contain “independent” describe separately constructed checks
within this AI workflow, not external human peer review.

## Steps awaiting independent review

The candidate conclusion depends on the correspondence between the
physical Hamiltonian, the analytic reductions, and the coded matrices.
Independent review is still needed for the normalization and normal
ordering; the recoupling identities and common-kernel identification;
the finite-sphere transfer and Schur averages; the coherent comparison
inequalities and positive many-body lifting; and the correspondence
between those formulas and all inputs to the interval verifier.

The arithmetic replay is not a proof-assistant formalization. No external
peer review or independent human validation is recorded for v0.1. The
publication status is therefore **candidate proof**, with the proposed
bound and its assumptions stated in the manuscript. The threshold
$Q_0=3088$ is not claimed to be the smallest possible sufficient threshold.

## Lean development after v0.1

On 7 October 2026, OpenAI Codex generated the initial 22-lemma Lean package
under Xin Shen's direction, then extended it to the coherent occupation
bound and its lift through the actual normalized pair annihilator. A subsequent
extension proves the normal-order decomposition, the four-body Fock quadratic
form, and the three-particle Gram and Hamiltonian identities. Separate
AI agents developed the tensor/Fock correspondence, coherent-pair estimates,
and operator identities, and reviewed their mathematical scope and normalization.
The package proves the occupation results in every finite particle sector, with no cutoff in
particle number or flux, and includes the exact quadratic-form correspondence
between the physical Hamiltonian and its Fock pair annihilators. The three-body
coefficient is identified with $2W_3TW_3^\dagger$ on three bosonic particles.

The recoupling extension connects the coefficient recurrence to the actual
compressed exchange T on the auxiliary pair-spin and spectator space
$V_Q\otimes U_Q$. It proves the full spectrum
$\lambda_z=(-1)^z(Q)_z/(2Q)_z$ for $0\le z\le Q$, its orthogonal spectral
projectors $\Pi_z$, and their exact ranks $3Q-2z+1$; $(Q)_z$ is a falling
factorial. The proof constructs highest-weight vectors of magnetic
weight $(3Q-2z)/2$ and their independent lowering descendants, using concrete
spin operators and their $\mathfrak{sl}_2$ commutators. It also proves the
Gram decomposition and
$S_{3,Q,3}=\sum_z2\lambda_zW_3\Pi_zW_3^\dagger$ on bosonic three-particle
states. AI agents wrote these formal proofs and performed the internal
semantic review. The complete eigenbasis uses the mathlib Hermitian-matrix
spectral theorem, credited in its
[pinned source](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Analysis/Matrix/Spectrum.lean)
to Alexander Bentkamp.

The subsequent three-body lift is defined on each finite M-particle sector by
$\mathcal L_3^{(M)}(A)=\binom M3P_M(A\otimes I_{M-3})P_M$ for $M\ge3$,
and zero below three particles. Here $P_M$ is the orthogonal bosonic
projection, and A is a complex linear map on the three-particle tensor space.
AI agents proved that this lift preserves positive quadratic forms, their
ordering, and self-adjointness. They checked its normalization on the
physical sector and proved $S_{3,Q,M}=\mathcal L_3^{(M)}(S_{3,Q,3})$.
They also constructed the normalized three-particle annihilation and
creation maps and proved the rank-one rule
$\mathcal L_3^{(M)}(|w\rangle\langle w'|)=A_M(w)^\dagger A_M(w')$,
including creation of bosonic w from vacuum.
The three-particle spectral formula is thereby lifted to every finite
particle sector and inserted into the actual $H_Q^2$ identity. Each lifted
block $\mathcal L_3^{(M)}(W_3\Pi_zW_3^\dagger)$ is proved positive and Hermitian.

The common-kernel extension proves that zero physical energy, membership
in the Hamiltonian kernel, and vanishing under every normalized V0 pair
annihilator are equivalent. AI agents constructed the exact total-orbital-deficit
blocks and their Hermitian positive Hamiltonian matrices, with Bose symmetry
imposed within the ordered-tensor coordinates. They also formalized the
invertible, nonunitary polynomial coordinate change, its induced positive
metric, and the correspondence between the physical annihilators and
unweighted polynomial pair channels.

For total deficit d and Q≥d, every occupied orbital label is at most d.
An explicit configuration bijection therefore transports the common
polynomial pair kernel between caps Q and d; composing with the coordinate
changes transports the physical zero spaces. The certificate row class
is proved to annihilate the physical kernel for arbitrary row coefficients.
On 8 October 2026, AI agents extended this bridge to complete occupation
and highest-weight coordinates. They proved the multiset/sorted-tuple
bijection, the factorial-weighted occupation inclusion, and the physical
normalization $\Phi_{Q,N,d}=\sqrt{Q^d/N!}D_Q^{-1}I_{\mathrm{occ}}$.
The resulting coordinates are proved injective and onto the physical
bosonic degree sector for Q>0. The agents derived the integer pair-removal
coefficients and the spherical diagonal metric from the physical maps,
then proved the Hamiltonian form with the verifier's
$\kappa_p^2/E_{p,Q}$ factors.

They also connected the integer center-of-mass derivative, with source
coefficient $j n_j$, to the actual angular-momentum raising operator.
The checked identity is $J_+\Phi_d=\sqrt Q\,\Phi_{d-1}C_d$ for d>0,
and the CM kernel is proved to represent the full physical highest-weight
space. The agents then verified the 26 retained rational frames: N=3 at
degrees 0–8 and N=4 at degrees 0–16. Clearing common denominators reduces
$CU=0$, $LU=I$, and $UL+VC=I$ to sparse integer identities checked by the
Lean kernel. A proved complete partition enumeration and exact CM-entry
checks connect the supplied arrays to the physical highest-weight spaces
for Q≥d>0. Separate degree-zero proofs cover every Q. The resulting bases
are generally nonorthogonal; their completeness is proved by explicit
linear equivalences and reconstruction.
The coordinate proofs do not import Python success flags as hypotheses.

In the planar-certificate extension, the Codex assistant proved the physical
form pullback, the inverse-metric Hamiltonian square, and its three-particle
normal-order consequence. It generated integer Gram and kernel witnesses
for all 26 exported planar comparison arrays and the corresponding 26
Hamiltonian arrays, then proved their common kernels and strict positivity
on the selected complements. Lean checks the exact witness identities;
Python supplies the proposed data and checks export reproducibility.
The assistant also performed the documented self-review. This extension
did not use a separate reviewing agent or add human verification.

The subsequent spherical-row extension was written and self-reviewed by
the Codex assistant. It derives exact pair and single-orbital annihilation
maps in the physical occupation coordinates, including their spherical
normalization. The four-body target is connected to a double-pair Gram
quadratic form. Explicit one- and two-particle transfer contractions prove
the certificate-row normal-order identities in the three- and four-particle
input sectors. Vacuum-functional identities and frozen-row scalar
cancellations then give the direct K3/K4 terms at matching degrees.
The extension uses arbitrary row coefficients; it does not claim that the
full frozen arrays, Schur average, or interval verifier have been formalized.
No additional human verification or separate reviewing agent was used.

All 1574 theorem declarations and 124 statement contracts pass the
full build and axiom audit, with pinned Lean/mathlib versions recorded.
The local build uses Lake package
overrides pointing to source archives of those same revisions. The only
axiom dependencies are `propext`, `Classical.choice`, and `Quot.sound`.
The [spherical-row build record](verification/lean_sphere_rows_build.json)
and [AI self-review](verification/audit_reports/lean_sphere_rows_audit.txt)
record the current physical-coordinate and normal-order checks.
The [planar-certificate build record](verification/lean_planar_certificates_build.json)
and [AI self-review](verification/audit_reports/lean_planar_certificates_audit.txt)
record the preceding planar extension.
The [retained-frame build record](verification/lean_retained_frames_build.json)
and [internal AI semantic audit](verification/audit_reports/lean_retained_frames_audit.txt)
record the frame and physical-basis checks. The
[occupation/highest-weight build record](verification/lean_occupation_highest_build.json)
and [audit](verification/audit_reports/lean_occupation_highest_audit.txt),
[common-kernel build record](verification/lean_common_kernel_build.json),
[three-body lift build record](verification/lean_three_body_lift_build.json),
[recoupling build record](verification/lean_recoupling_build.json) and
[normal-order build record](verification/lean_normal_order_build.json) remain
available as development history. No independent human review is claimed.

The remaining tasks include identifying the full comparison matrices,
proving the two-spectator and coherent-integral estimates,
and completing the finite-sphere transfer, averaging, and interval-certificate
proofs. Exact exported planar-array PSD, common kernels, and selected-complement
positivity are now proved. Identification of the full comparison arrays with
the physical operators, finite-sphere interval certificates, and the uniform
spectral-gap target remain unproved in Lean. The package's [status](lean/README.md) lists the
remaining proof chain. Neither the v0.1 PDF nor its release is replaced by
this code update.
