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
# Definitions: Weyl operators, the discrete Wigner function and stabilizer states

The definitions of D. Gross, "Hudson's theorem for finite-dimensional quantum systems",
*J. Math. Phys.* 47, 122107 (2006), arXiv:quant-ph/0602001, Section II. These are copied verbatim
into `Challenge.lean`.

The system is `n` qudits of dimension `d`. A vector is a function `ψ : (Fin n → ZMod d) → ℂ`,
the coefficients `ψ(x) = ⟨x|ψ⟩` in the computational basis.
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
for some isotropic subgroup `M` of phase space with `dⁿ` elements, which is Gross's definition of
a maximally isotropic subspace (Section II D; additive subgroups of `ℤ_d²ⁿ` are its subspaces).
Gross's Lemma 8 names the eigenvalues, `ω([v, m]) w(m) ψ = ψ`; `isStabilizerState_iff_exists_vec`
proves that the two forms agree. The zero vector satisfies this definition; Gross's state vectors
are non-zero. -/
def IsStabilizerState (ψ : Config d n → ℂ) : Prop :=
  ∃ M : AddSubgroup (PhaseSpace d n), (∀ u ∈ M, ∀ v ∈ M, symp u v = 0) ∧
    Nat.card M = d ^ n ∧ ∀ m ∈ M, ∃ c : ℂ, weyl m ψ = c • ψ

end DiscreteHudson
