# The discrete Hudson theorem, in Lean

**Theorem** (D. Gross, "Hudson's theorem for finite-dimensional quantum systems", *J. Math. Phys.* 47 (2006) 122107, arXiv:quant-ph/0602001, Theorem 2). For odd d, a pure state of n qudits has a non-negative Wigner function if and only if it is a stabilizer state.

Hudson proved in 1974 that a pure state of a continuous-variable system has a non-negative Wigner function exactly when it is Gaussian. Gross's theorem is the finite-dimensional version, with stabilizer states in place of Gaussian states. It is why negative values of the discrete Wigner function are treated as a resource for quantum computation. Stabilizer states can be simulated efficiently on a classical computer (the Gottesman–Knill theorem). A state with a negative Wigner value, such as a magic state, is needed to go beyond them.

This repository proves it in Lean 4 with Mathlib, for every odd d, prime or not, and every number of qudits n.

## The statements

A vector of n qudits is a function `ψ : (Fin n → ZMod d) → ℂ` on the computational basis. The definitions are Gross's (Section II), with `ω(t) = e^{2πit/d}`:

- the **Weyl operators** `(w(p, q) ψ)(x) = ω(−2⁻¹ p·q + p·x) ψ(x − q)` (`weyl`);
- the **symplectic form** `[(p, q), (p′, q′)] = p·q′ − q·p′` (`symp`);
- the **phase point operators** `A(a) = d⁻ⁿ Σ_b ω([a, b]) w(b)` (`phasePoint`);
- the **Wigner function** `W(a) = d⁻ⁿ ⟨ψ| A(a) |ψ⟩` (`wigner`), Gross's Definition 5. For a vector that isn't normalised this is ‖ψ‖² times Gross's W, which doesn't change its sign;
- a **stabilizer state** is a common eigenvector of the Weyl operators `w(m)`, `m ∈ M`, for an isotropic subgroup `M` of phase space with `dⁿ` elements (`IsStabilizerState`). Gross's Lemma 8 defines it this way, with the eigenvalues named, and his Corollary 26 shows these subgroups are exactly the maximally isotropic ones.

```lean
theorem DiscreteHudson.discrete_hudson (hd : Odd d) (ψ : Config d n → ℂ) (hψ : ψ ≠ 0) :
    (∀ a, 0 ≤ wigner ψ a) ↔ IsStabilizerState ψ

theorem DiscreteHudson.wigner_im (hd : Odd d) (ψ : Config d n → ℂ) (a : PhaseSpace d n) :
    (wigner ψ a).im = 0

theorem DiscreteHudson.wigner_eq (hd : Odd d) (ψ : Config d n → ℂ) (p q : Config d n) :
    wigner ψ (p, q) = ((d : ℂ) ^ n)⁻¹ * ∑ ξ : Config d n, ZMod.stdAddChar (p ⬝ᵥ ξ) *
      (star (ψ (q + (2 : ZMod d)⁻¹ • ξ)) * ψ (q - (2 : ZMod d)⁻¹ • ξ))
```

- `discrete_hudson` is Gross's Theorem 2. `0 ≤ wigner ψ a` uses Mathlib's `ComplexOrder`, in which `0 ≤ z` means that z is real and non-negative.
- `wigner_im` says the Wigner function is real (Gross, Theorem 6.1), so that condition is ordinary non-negativity.
- `wigner_eq` is the closed form of Gross's Theorem 6.2.

## The proof

The proof does not follow Gross's Section III, which uses a discrete Bochner theorem, "balanced sets", Clifford covariance and a similarity lemma for composite d. It uses the algebra of the phase point operators instead. I don't claim the route is new. Write `e(a) = ⟨ψ|A(a)|ψ⟩` and `N = ‖ψ‖²`.

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

## Checks

- **Axioms.** `audit/Axioms.lean` uses `#guard_msgs` to require that the three theorems and both directions of the main argument use only `propext`, `Classical.choice` and `Quot.sound`.
- **Non-vacuity.** `audit/Control.lean` shows that both sides of the equivalence are attained:
  - the basis vector `|0⋯0⟩` is a stabilizer state for every d and n, so its Wigner function is non-negative;
  - for one qutrit, the Norrell state `|1⟩ − |2⟩` has `W(0, 0) = −2/3` (−1/3 once normalised), so it is not a stabilizer state.

  A canary at the end confirms that the axiom audit catches `sorry`.
- **CI** rebuilds the library and `Solution` with warnings as errors, runs both audits, checks `formalization.yaml`, and runs `lake comparator`.
- **Comparator.** `scripts/verify-comparator.sh` runs `lake comparator` in CI, sandboxed on Linux. It checks `Challenge.lean` against the proof and replays the proof through Lean's kernel, nanoda and con-ron.
  - I have run it locally on Windows, unsandboxed (`--inadvisably-no-sandbox`, with full paths to the nanoda and con-ron binaries in a copy of `comparator.json`), on 25 November 2026.
  - It ended "Your solution is okay!", with con-ron (18,928 declarations), nanoda and Lean's kernel all accepting the proof.
  - An unsandboxed run is not the trusted check; the sandboxed Linux run in CI is.

## Related work

- **No earlier Lean proof of the theorem that I could find.** dbccpage/19L57G1 checks small cases on explicit tables, but doesn't state the theorem:
  - [`NonclassicalHorizons.lean`](https://github.com/dbccpage/19L57G1/blob/f7bc4af97ed616c9f03c791dc038ae65146bd9ff/research/p209d_nonclassical_horizons/lean/NonclassicalHorizons.lean), `discrete_hudson_boundary_separation`: one stabilizer Wigner table of a qutrit is non-negative, and the Norrell state is negative at the origin;
  - [`WignerPhaseSpace.lean`](https://github.com/dbccpage/19L57G1/blob/f7bc4af97ed616c9f03c791dc038ae65146bd9ff/research/p209a_wigner_phase_space/lean/WignerPhaseSpace.lean): parity-operator checks for d = 3 and 5.
- **Searches, 25 November 2026.** None of these is proof that nothing else exists.
  - GitHub code search for Lean files mentioning Hudson, discrete Wigner functions, phase point operators, stabilizer states with Wigner functions, Wigner negativity, Weyl operators over `ZMod`, and Heisenberg–Weyl.
  - The Palomar registry.
  - Mathlib, Physlib, QICLean, Lean-QIT and Lean-QuantumInfo.

## Files

- `Challenge.lean` states the three theorems, ending in `sorry`. It imports only Mathlib.
- `DiscreteHudson/Defs.lean`: the definitions, as in `Challenge.lean`.
- `DiscreteHudson/Basic.lean`: inverting 2, roots of unity, character sums and Parseval on `ℤ_dⁿ`.
- `DiscreteHudson/Weyl.lean`, `Sums.lean`, `Hudson.lean`: the proof.
- `DiscreteHudson/Main.lean`: the three theorems as stated in `Challenge.lean`. `Solution.lean` re-exports them.

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
