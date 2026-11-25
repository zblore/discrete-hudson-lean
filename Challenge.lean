/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Group.Subgroup.Defs

/-!
# The discrete Hudson theorem

D. Gross, "Hudson's theorem for finite-dimensional quantum systems", arXiv:quant-ph/0602001,
Theorem 2: for odd `d`, a pure state of `n` qudits has a non-negative Wigner function if and only
if it is a stabilizer state.

The definitions follow Gross's Section II and are those of `DiscreteHudson/Defs.lean`, verbatim.
A vector is a function `ψ : (Fin n → ZMod d) → ℂ` on the computational basis.

* `weyl v` is the Weyl operator `w(p, q)`, `(w(p, q) ψ)(x) = ω(-2⁻¹ p·q + p·x) ψ(x - q)`, with
  `ω(t) = e^{2πit/d}` (`ZMod.stdAddChar`).
* `phasePoint a` is `A(a) = d⁻ⁿ Σ_b ω([a, b]) w(b)`, with `[(p, q), (p', q')] = p·q' - q·p'`.
* `wigner ψ a` is `W(a) = d⁻ⁿ ⟨ψ| A(a) |ψ⟩`: Gross's Wigner function for a unit vector, and that
  function times `‖ψ‖²` in general.
* `IsStabilizerState ψ`: `ψ` is a common eigenvector of the `w(m)`, `m ∈ M`, for an isotropic
  subgroup `M` of phase space with `dⁿ` elements (Gross, Lemma 8 and Corollary 26).

The theorems:

* `wigner_im`: the Wigner function is real (so `0 ≤ wigner ψ a`, in `ComplexOrder`, says only
  that it is non-negative);
* `wigner_eq`: the closed form `W(p, q) = d⁻ⁿ Σ_ξ ω(p · ξ) ψ̄(q + ξ/2) ψ(q - ξ/2)`;
* `discrete_hudson`: Gross's Theorem 2.
-/

@[expose] public section

open scoped ComplexOrder

namespace DiscreteHudson

/-- Configuration space `Q = ℤ_dⁿ`: the labels of the computational basis. -/
abbrev Config (d n : ℕ) := Fin n → ZMod d

/-- Phase space `V = Q × Q`. A point `v = (p, q)` has momentum `p` and position `q`. -/
abbrev PhaseSpace (d n : ℕ) := Config d n × Config d n

variable {d n : ℕ} [NeZero d]

/-- The symplectic form `[(p, q), (p', q')] = p · q' - q · p'` (Gross, eqs. (5) and (6)). -/
def symp (a b : PhaseSpace d n) : ZMod d := a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1

/-- The Weyl operator `w(p, q)`, acting by `(w(p, q) ψ)(x) = ω(-2⁻¹ p·q + p·x) ψ(x - q)`
(Gross, eqs. (3) and (8)), where `ω(t) = e^{2πit/d}` is `ZMod.stdAddChar`. -/
noncomputable def weyl (v : PhaseSpace d n) (ψ : Config d n → ℂ) : Config d n → ℂ :=
  fun x => ZMod.stdAddChar (-((2 : ZMod d)⁻¹ * (v.1 ⬝ᵥ v.2)) + v.1 ⬝ᵥ x) * ψ (x - v.2)

/-- The phase point operator `A(a) = d⁻ⁿ Σ_b ω([a, b]) w(b)` (Gross, eq. (15)). -/
noncomputable def phasePoint (a : PhaseSpace d n) (ψ : Config d n → ℂ) : Config d n → ℂ :=
  fun x => ((d : ℂ) ^ n)⁻¹ * ∑ b : PhaseSpace d n, ZMod.stdAddChar (symp a b) * weyl b ψ x

/-- The Wigner function `W(a) = d⁻ⁿ ⟨ψ| A(a) |ψ⟩` (Gross, Definition 5 and eq. (15), with
`ρ = |ψ⟩⟨ψ|`). For a unit vector this is Gross's Wigner function; in general it is that function
times `‖ψ‖²`, which does not change its sign. -/
noncomputable def wigner (ψ : Config d n → ℂ) (a : PhaseSpace d n) : ℂ :=
  ((d : ℂ) ^ n)⁻¹ * ∑ x, star (ψ x) * phasePoint a ψ x

/-- `ψ` is a stabilizer state: it is a common eigenvector of the Weyl operators `w(m)`, `m ∈ M`,
for some isotropic subgroup `M` of phase space with `dⁿ` elements, that is, a maximally
isotropic one (Gross, Lemma 8 and Corollary 26). -/
def IsStabilizerState (ψ : Config d n → ℂ) : Prop :=
  ∃ M : AddSubgroup (PhaseSpace d n), (∀ u ∈ M, ∀ v ∈ M, symp u v = 0) ∧
    Nat.card M = d ^ n ∧ ∀ m ∈ M, ∃ c : ℂ, weyl m ψ = c • ψ


/-- The Wigner function is real. -/
theorem wigner_im (hd : Odd d) (ψ : Config d n → ℂ) (a : PhaseSpace d n) :
    (wigner ψ a).im = 0 := by
  sorry

/-- The Wigner function in closed form:
`W(p, q) = d⁻ⁿ Σ_ξ ω(p · ξ) ψ̄(q + ξ/2) ψ(q - ξ/2)`. -/
theorem wigner_eq (hd : Odd d) (ψ : Config d n → ℂ) (p q : Config d n) :
    wigner ψ (p, q) = ((d : ℂ) ^ n)⁻¹ * ∑ ξ : Config d n, ZMod.stdAddChar (p ⬝ᵥ ξ) *
      (star (ψ (q + (2 : ZMod d)⁻¹ • ξ)) * ψ (q - (2 : ZMod d)⁻¹ • ξ)) := by
  sorry

/-- **The discrete Hudson theorem** (Gross, Theorem 2). For odd `d`, a non-zero vector of `n`
qudits has a non-negative Wigner function if and only if it is a stabilizer state. -/
theorem discrete_hudson (hd : Odd d) (ψ : Config d n → ℂ) (hψ : ψ ≠ 0) :
    (∀ a, 0 ≤ wigner ψ a) ↔ IsStabilizerState ψ := by
  sorry

end DiscreteHudson
