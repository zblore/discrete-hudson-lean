/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import DiscreteHudson.Hudson

/-!
# The discrete Hudson theorem

The statements of `Challenge.lean`, proved from the rest of the library.
-/

@[expose] public section

open scoped ComplexOrder

namespace DiscreteHudson

variable {d n : ℕ} [NeZero d]

/-- The Wigner function is real. -/
theorem wigner_im (hd : Odd d) (ψ : Config d n → ℂ) (a : PhaseSpace d n) :
    (wigner ψ a).im = 0 := by
  have h1 := Complex.conj_eq_iff_re.1 (star_inner_phasePoint hd a ψ)
  rw [wigner, ← h1, ← Complex.ofReal_natCast, ← Complex.ofReal_pow, ← Complex.ofReal_inv,
    ← Complex.ofReal_mul, Complex.ofReal_im]

/-- The Wigner function in closed form, `W(p, q) = d⁻ⁿ Σ_ξ ω(p · ξ) ψ̄(q + ξ/2) ψ(q - ξ/2)`. This is
Gross's Theorem 6.2 after the substitution `ξ ↦ -ξ`. -/
theorem wigner_eq (hd : Odd d) (ψ : Config d n → ℂ) (p q : Config d n) :
    wigner ψ (p, q) = ((d : ℂ) ^ n)⁻¹ * ∑ ξ : Config d n, ZMod.stdAddChar (p ⬝ᵥ ξ) *
      (star (ψ (q + (2 : ZMod d)⁻¹ • ξ)) * ψ (q - (2 : ZMod d)⁻¹ • ξ)) := by
  rw [wigner, inner_phasePoint_eq hd]

/-- **The discrete Hudson theorem** (Gross, Theorem 2). For odd `d`, a vector of `n` qudits has a
non-negative Wigner function if and only if it is a stabilizer state. (The zero vector satisfies
both sides.) -/
theorem discrete_hudson (hd : Odd d) (ψ : Config d n → ℂ) :
    (∀ a, 0 ≤ wigner ψ a) ↔ IsStabilizerState ψ :=
  ⟨isStabilizerState_of_nonneg hd ψ, wigner_nonneg_of_isStabilizerState hd ψ⟩

end DiscreteHudson
