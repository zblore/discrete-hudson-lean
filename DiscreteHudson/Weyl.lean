/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import DiscreteHudson.Basic

/-!
# The algebra of Weyl and phase point operators

For odd `d`:

* `weyl_mul`: `w(u) w(v) = ω(2⁻¹ [u, v]) w(u + v)` (Gross, eq. (4));
* `weyl_comm`: `w(u) w(v) = ω([u, v]) w(v) w(u)`;
* `phasePoint_apply`: `(A(a) ψ)(x) = ω(2 p · (x - q)) ψ(2q - x)` for `a = (p, q)`;
* `phasePoint_phasePoint_self`: `A(a)² = 1`;
* `inner_phasePoint`: `A(a)` is self-adjoint;
* `phasePoint_phasePoint`: `A(a) A(b) = ω(2 [b, a]) w(2(a - b))`.
-/

@[expose] public section

open Finset

namespace DiscreteHudson

variable {d n : ℕ} [NeZero d]

local notation "ω" => (ZMod.stdAddChar : AddChar (ZMod d) ℂ)

omit [NeZero d] in
lemma symp_self (u : PhaseSpace d n) : symp u u = 0 := by
  simp [symp, dotProduct_comm u.1]

omit [NeZero d] in
lemma symp_comm (u v : PhaseSpace d n) : symp v u = -symp u v := by
  simp only [symp]; rw [dotProduct_comm v.1, dotProduct_comm v.2]; ring

lemma weyl_zero (ψ : Config d n → ℂ) : weyl 0 ψ = ψ := by
  funext x; simp [weyl]

lemma weyl_mul (hd : Odd d) (u v : PhaseSpace d n) (ψ : Config d n → ℂ) :
    weyl u (weyl v ψ) = ω ((2 : ZMod d)⁻¹ * symp u v) • weyl (u + v) ψ := by
  funext x
  simp only [weyl, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add]
  rw [show x - u.2 - v.2 = x - (u.2 + v.2) by abel, ← mul_assoc, ← mul_assoc,
    ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [symp, add_dotProduct, dotProduct_add, dotProduct_sub]
  rw [dotProduct_comm u.2 v.1]
  linear_combination (v.1 ⬝ᵥ u.2) * inv_two_mul_two hd

omit [NeZero d] in
lemma half_add_half (hd : Odd d) : (2 : ZMod d)⁻¹ + 2⁻¹ = 1 := by
  rw [← two_mul, two_mul_inv_two hd]

lemma weyl_comm (hd : Odd d) (u v : PhaseSpace d n) (ψ : Config d n → ℂ) :
    weyl u (weyl v ψ) = ω (symp u v) • weyl v (weyl u ψ) := by
  rw [weyl_mul hd, weyl_mul hd, add_comm v u, smul_smul, ← AddChar.map_add_eq_mul]
  congr 2
  linear_combination (-(2 : ZMod d)⁻¹) * symp_comm u v + symp u v * half_add_half hd

lemma weyl_neg_weyl (hd : Odd d) (u : PhaseSpace d n) (ψ : Config d n → ℂ) :
    weyl (-u) (weyl u ψ) = ψ := by
  rw [weyl_mul hd, neg_add_cancel, weyl_zero]
  have : symp (-u) u = 0 := by simp [symp, dotProduct_comm u.1]
  rw [this, mul_zero, AddChar.map_zero_eq_one, one_smul]

/-- The Weyl operators preserve the norm. -/
lemma norm_weyl (v : PhaseSpace d n) (ψ : Config d n → ℂ) :
    ∑ x, star (weyl v ψ x) * weyl v ψ x = ∑ x, star (ψ x) * ψ x := by
  have : ∀ x, star (weyl v ψ x) * weyl v ψ x = star (ψ (x - v.2)) * ψ (x - v.2) := by
    intro x
    simp only [weyl, star_mul']
    calc star (ω _) * star (ψ (x - v.2)) * (ω _ * ψ (x - v.2))
        = (star (ω _) * ω _) * (star (ψ (x - v.2)) * ψ (x - v.2)) := by ring
      _ = _ := by rw [star_char_mul, one_mul]
  simp_rw [this]
  exact Fintype.sum_equiv (Equiv.subRight v.2) _ _ (fun _ => rfl)

omit [NeZero d] in
lemma cond_iff (hd : Odd d) (x q q' : Config d n) :
    x - q - (2 : ZMod d)⁻¹ • q' = 0 ↔ (2 : ZMod d) • (x - q) = q' := by
  constructor
  · intro h
    rw [sub_eq_zero] at h
    rw [h, smul_smul, two_mul_inv_two hd, one_smul]
  · intro h
    rw [← h, smul_smul, inv_two_mul_two hd, one_smul, sub_self]

/-- The explicit form of the phase point operators: `A(a)` reflects through the position `q`
and multiplies by a phase. In particular `A(0)` is the parity operator `ψ(x) ↦ ψ(-x)`. -/
lemma phasePoint_apply (hd : Odd d) (a : PhaseSpace d n) (ψ : Config d n → ℂ) (x : Config d n) :
    phasePoint a ψ x = ω (2 * (a.1 ⬝ᵥ (x - a.2))) * ψ ((2 : ZMod d) • a.2 - x) := by
  have hdn : ((d : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne d))
  simp only [phasePoint, weyl]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have step : ∀ q' p' : Config d n,
      ω (symp a (p', q')) * (ω (-((2 : ZMod d)⁻¹ * ((p', q').1 ⬝ᵥ (p', q').2)) +
        (p', q').1 ⬝ᵥ x) * ψ (x - (p', q').2)) =
      ω (p' ⬝ᵥ (x - a.2 - (2 : ZMod d)⁻¹ • q')) * (ω (a.1 ⬝ᵥ q') * ψ (x - q')) := by
    intro q' p'
    simp only [symp]
    rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 2
    simp only [dotProduct_sub, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm a.2 p']
    ring
  simp_rw [step, ← Finset.sum_mul, sum_char_dot, cond_iff hd, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_univ, ↓reduceIte]
  rw [← mul_assoc, inv_mul_cancel₀ hdn, one_mul]
  congr 2
  · simp only [dotProduct_smul, smul_eq_mul]
  · rw [smul_sub, two_smul, two_smul]; abel

lemma phasePoint_phasePoint_self (hd : Odd d) (a : PhaseSpace d n) (ψ : Config d n → ℂ) :
    phasePoint a (phasePoint a ψ) = ψ := by
  funext x
  rw [phasePoint_apply hd, phasePoint_apply hd, ← mul_assoc, ← AddChar.map_add_eq_mul,
    show (2 : ZMod d) • a.2 - ((2 : ZMod d) • a.2 - x) = x by abel]
  have : 2 * (a.1 ⬝ᵥ (x - a.2)) + 2 * (a.1 ⬝ᵥ ((2 : ZMod d) • a.2 - x - a.2)) = 0 := by
    rw [show (2 : ZMod d) • a.2 - x - a.2 = -(x - a.2) by rw [two_smul]; abel, dotProduct_neg]
    ring
  rw [this, AddChar.map_zero_eq_one, one_mul]

/-- `A(a)` is self-adjoint. -/
lemma inner_phasePoint (hd : Odd d) (a : PhaseSpace d n) (φ ψ : Config d n → ℂ) :
    ∑ x, star (φ x) * phasePoint a ψ x = ∑ x, star (phasePoint a φ x) * ψ x := by
  simp_rw [phasePoint_apply hd, star_mul', star_char]
  refine Fintype.sum_equiv (Equiv.subLeft ((2 : ZMod d) • a.2)) _ _ (fun x => ?_)
  simp only [Equiv.subLeft_apply, sub_sub_cancel]
  rw [show (2 : ZMod d) • a.2 - x - a.2 = -(x - a.2) by rw [two_smul]; abel, dotProduct_neg,
    mul_neg, neg_neg]
  ring

/-- The product of two phase point operators is a Weyl operator, up to a phase. -/
lemma phasePoint_phasePoint (hd : Odd d) (a b : PhaseSpace d n) (ψ : Config d n → ℂ) :
    phasePoint a (phasePoint b ψ) = ω (2 * symp b a) • weyl ((2 : ZMod d) • (a - b)) ψ := by
  funext x
  rw [phasePoint_apply hd, phasePoint_apply hd]
  simp only [weyl, Pi.smul_apply, smul_eq_mul, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
    Prod.snd_sub]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  · simp only [symp, sub_dotProduct, dotProduct_sub, dotProduct_smul, smul_dotProduct,
      smul_eq_mul]
    linear_combination (2 * (a.1 ⬝ᵥ a.2 - b.1 ⬝ᵥ a.2 - a.1 ⬝ᵥ b.2 + b.1 ⬝ᵥ b.2)) *
      inv_two_mul_two hd + 2 * dotProduct_comm b.2 a.1
  · rw [smul_sub]; abel

end DiscreteHudson
