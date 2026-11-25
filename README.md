# The discrete Hudson theorem, in Lean

**Theorem** (D. Gross, "Hudson's theorem for finite-dimensional quantum systems", *J. Math. Phys.* 47 (2006) 122107, arXiv:quant-ph/0602001, Theorem 2). For odd d, a pure state of n qudits has a non-negative Wigner function if and only if it is a stabilizer state.

Hudson proved in 1974 that a pure state of a continuous-variable system has a non-negative Wigner function exactly when it is Gaussian. Gross's theorem is the finite-dimensional version, with stabilizer states in place of Gaussian states. Circuits built from stabilizer states and Clifford gates can be simulated efficiently on a classical computer (the Gottesman–Knill theorem). In odd dimensions, negative values of the Wigner function are used to measure how far a state lies outside that classically simulable setting (Veitch, Mousavian, Gottesman and Emerson, arXiv:1307.7171). For pure states, this theorem says that negativity is exactly what separates a state from the stabilizer states. For mixed states it is not: Gross gives a mixed state with a non-negative Wigner function that is not a mixture of stabilizer states.

This repository proves it in Lean 4 with Mathlib, for every odd d, prime or not, and every number of qudits n.

## The statements

A vector of n qudits is a function `ψ : (Fin n → ZMod d) → ℂ` on the computational basis. The definitions are Gross's (Section II), with `ω(t) = e^{2πit/d}`:

- the **Weyl operators** `(w(p, q) ψ)(x) = ω(−2⁻¹ p·q + p·x) ψ(x − q)` (`weyl`);
- the **symplectic form** `[(p, q), (p′, q′)] = p·q′ − q·p′` (`symp`);
- the **phase point operators** `A(a) = d⁻ⁿ Σ_b ω([a, b]) w(b)` (`phasePoint`);
- the **Wigner function** `W(a) = d⁻ⁿ ⟨ψ| A(a) |ψ⟩` (`wigner`), Gross's Definition 5. For a vector that isn't normalised this is ‖ψ‖² times Gross's W, which doesn't change its sign;
- a **stabilizer state** is a common eigenvector of the Weyl operators `w(m)`, `m ∈ M`, for an isotropic subgroup `M` of phase space with `dⁿ` elements (`IsStabilizerState`). An isotropic subspace with `dⁿ` elements is Gross's definition of a maximally isotropic one (Section II D); for composite d, his subspaces are the additive subgroups. His Lemma 8 names the eigenvalues, `ω([v, m]) w(m) ψ = ψ`, and `isStabilizerState_iff_exists_vec` proves that form is equivalent. The zero vector satisfies both sides of the theorem, so no non-zero hypothesis is needed.

```lean
theorem DiscreteHudson.discrete_hudson (hd : Odd d) (ψ : Config d n → ℂ) :
    (∀ a, 0 ≤ wigner ψ a) ↔ IsStabilizerState ψ

theorem DiscreteHudson.isStabilizerState_iff_exists_vec (hd : Odd d) (ψ : Config d n → ℂ) :
    IsStabilizerState ψ ↔ ∃ M : AddSubgroup (PhaseSpace d n),
      (∀ u ∈ M, ∀ v ∈ M, symp u v = 0) ∧ Nat.card M = d ^ n ∧
        ∃ v : PhaseSpace d n, ∀ m ∈ M, ZMod.stdAddChar (symp v m) • weyl m ψ = ψ

theorem DiscreteHudson.wigner_im (hd : Odd d) (ψ : Config d n → ℂ) (a : PhaseSpace d n) :
    (wigner ψ a).im = 0

theorem DiscreteHudson.wigner_eq (hd : Odd d) (ψ : Config d n → ℂ) (p q : Config d n) :
    wigner ψ (p, q) = ((d : ℂ) ^ n)⁻¹ * ∑ ξ : Config d n, ZMod.stdAddChar (p ⬝ᵥ ξ) *
      (star (ψ (q + (2 : ZMod d)⁻¹ • ξ)) * ψ (q - (2 : ZMod d)⁻¹ • ξ))
```

- `discrete_hudson` is Gross's Theorem 2. `0 ≤ wigner ψ a` uses Mathlib's `ComplexOrder`, in which `0 ≤ z` means that z is real and non-negative.
- `wigner_im` says the Wigner function is real (Gross, Theorem 6.1), so that condition is ordinary non-negativity.
- `wigner_eq` is the closed form of Gross's Theorem 6.2, after the substitution ξ ↦ −ξ.
- `isStabilizerState_iff_exists_vec` is Gross's Lemma 8 form of a stabilizer state.

## The proof

The proof does not follow Gross's Section III, which uses a discrete Bochner theorem, "balanced sets", Clifford covariance and a similarity lemma for composite d. It follows the shorter route of D. Gross, S. Nezami and M. Walter, "Schur–Weyl duality for the Clifford group with applications", *Commun. Math. Phys.* 385 (2021) 1325–1393, arXiv:1712.08628, Section 8.1. I worked it out before reading their paper, and learned of it from a review. They get isotropy from products of three phase point operators. Here products of two give a group of Weyl operators, and its size is bounded directly. Write `e(a) = ⟨ψ|A(a)|ψ⟩` and `N = ‖ψ‖²`.

1. **The operators** (`DiscreteHudson/Weyl.lean`).
   - The Weyl operators compose as `w(u) w(v) = ω(2⁻¹[u, v]) w(u + v)`.
   - `A(a)` reflects through the position q and multiplies by a phase: `(A(p, q) ψ)(x) = ω(2 p·(x − q)) ψ(2q − x)`.
   - So `A(a)` is a self-adjoint involution.
   - The product of two of them is a Weyl operator up to a phase: `A(a) A(b) = ω(2[b, a]) w(2(a − b))`.
2. **Sums over phase space** (`DiscreteHudson/Sums.lean`). Using character orthogonality on `ℤ_dⁿ` and Parseval:
   - `Σ_a e(a) = dⁿ N`;
   - `Σ_a |e(a)|² = dⁿ N²`;
   - `Σ_v |⟨ψ|w(v)|ψ⟩|² = dⁿ N²`.
3. **Non-negative implies stabilizer** (`DiscreteHudson/Hudson.lean`).
   - `A(a)` is a self-adjoint involution, so `e(a)` is real and at most N, with equality only if `A(a) ψ = ψ`.
   - If every `e(a) ≥ 0`, then `Σ_a e(a)(N − e(a)) = 0` with non-negative terms. So each `e(a)` is 0 or N, and the set S where it equals N has `dⁿ` points.
   - For `a, a₀ ∈ S`, `A(a) A(a₀)` fixes ψ, so ψ is an eigenvector of `w(2(a − a₀))`, and of every Weyl operator in the subgroup M these generate.
   - **M is isotropic.** A common eigenvector forces two Weyl operators to commute.
   - **`|M| ≥ dⁿ`.** 2 is invertible mod d, so `a ↦ 2(a − a₀)` is injective.
   - **`|M| ≤ dⁿ`.** Each `v ∈ M` contributes N² to `Σ_v |⟨ψ|w(v)|ψ⟩|² = dⁿ N²`.
4. **Stabilizer implies non-negative** (Gross's Lemma 9).
   - The same identity forces `⟨ψ|w(v)|ψ⟩ = 0` for v outside M.
   - On an isotropic M the eigenvalues form a character, so `e(a)` is `N/dⁿ` times a character sum over M.
   - That sum is either |M| or 0, so `e(a) ≥ 0`.
   - When it is |M|, the character is trivial, which is Gross's Lemma 8 form with `v = a`. Since `Σ_a e(a) = dⁿ N ≠ 0`, some a has this, which proves `isStabilizerState_iff_exists_vec`.

## Checks

- **Axioms.** `audit/Axioms.lean` uses `#guard_msgs` to require that the four theorems and both directions of the main argument use only `propext`, `Classical.choice` and `Quot.sound`.
- **Non-vacuity.** `audit/Control.lean` shows that both sides of the equivalence are attained:
  - the basis vector `|0⋯0⟩` is a stabilizer state for every d and n, so its Wigner function is non-negative;
  - for one qutrit, the Strange state `|1⟩ − |2⟩` (in the naming of Veitch et al.) has `W(0, 0) = −2/3` (−1/3 once normalised), so it is not a stabilizer state;
  - for d = 9, the vector `|0⟩ + |3⟩ + |6⟩` is a stabilizer state for `M = 3ℤ₉ × 3ℤ₉`, which is not a subspace over a field, so the theorem is exercised at a composite dimension.

  A canary at the end confirms that the axiom audit catches `sorry`.
- **CI** rebuilds the library and `Solution` with warnings as errors, runs both audits, checks `formalization.yaml`, and runs `lake comparator`.
- **Comparator.** `scripts/verify-comparator.sh` runs `lake comparator` in CI, sandboxed on Linux. It checks `Challenge.lean` against the proof and replays the proof through Lean's kernel, nanoda and con-ron.
  - I have run it locally on Windows, unsandboxed (`--inadvisably-no-sandbox`, with full paths to the nanoda and con-ron binaries in a copy of `comparator.json`), on 25 November 2026.
  - It ended "Your solution is okay!", with con-ron (19,020 declarations), nanoda and Lean's kernel all accepting the proof.
  - An unsandboxed run is not the trusted check; the sandboxed Linux run in CI is.

## Related work

- **The proof route** is that of Gross, Nezami and Walter, Section 8.1 (above). Their proof is on paper.
- **No earlier formal proof of the theorem that I could find.** dbccpage/19L57G1 checks small cases on explicit tables, but doesn't state the theorem:
  - [`NonclassicalHorizons.lean`](https://github.com/dbccpage/19L57G1/blob/f7bc4af97ed616c9f03c791dc038ae65146bd9ff/research/p209d_nonclassical_horizons/lean/NonclassicalHorizons.lean), `discrete_hudson_boundary_separation`: one stabilizer Wigner table of a qutrit is non-negative, and the state `(|1⟩ − |2⟩)/√2` is negative at the origin. The file calls it `W_magic_norrell`; Veitch et al. call that state the Strange state;
  - [`WignerPhaseSpace.lean`](https://github.com/dbccpage/19L57G1/blob/f7bc4af97ed616c9f03c791dc038ae65146bd9ff/research/p209a_wigner_phase_space/lean/WignerPhaseSpace.lean): parity-operator checks for d = 3 and 5.
- **Searches, 25 November 2026.** None of these is proof that nothing else exists.
  - GitHub code search for Lean files mentioning Hudson, discrete Wigner functions, phase point operators, stabilizer states with Wigner functions, Wigner negativity, Weyl operators over `ZMod`, and Heisenberg–Weyl.
  - The Palomar registry.
  - Mathlib, Physlib, QICLean, Lean-QIT and Lean-QuantumInfo.

## Files

- `Challenge.lean` states the four theorems, ending in `sorry`. It imports only Mathlib, and a plain `lake build` prints its four `sorry` warnings, as expected.
- `DiscreteHudson/Defs.lean`: the definitions, as in `Challenge.lean`.
- `DiscreteHudson/Basic.lean`: inverting 2, roots of unity, character sums and Parseval on `ℤ_dⁿ`.
- `DiscreteHudson/Weyl.lean`, `Sums.lean`, `Hudson.lean`: the proof.
- `DiscreteHudson/Main.lean`: three of the theorems as stated in `Challenge.lean`; `isStabilizerState_iff_exists_vec` is in `Hudson.lean`. `Solution.lean` re-exports them.

## Building

Lean `v4.35.0-rc3` and Mathlib `5e0c4e5239cb0a2d86d68a884bf52cfd963fce22`.

```
lake exe cache get
lake build
lake env lean audit/Axioms.lean
lake env lean audit/Control.lean
python3 scripts/check-lean-sources.py
ruby scripts/validate-formalization.rb
```

## How it was made

I drafted the Lean with Claude Code.

## Licence

Apache 2.0.
