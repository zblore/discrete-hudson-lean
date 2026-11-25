/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import DiscreteHudson.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Basic facts: `2` is invertible, roots of unity, character sums, Parseval
-/

@[expose] public section

open Finset

namespace DiscreteHudson

variable {d n : ℕ} [NeZero d]

/-- Shorthand for `ω = ZMod.stdAddChar`. -/
local notation "ω" => (ZMod.stdAddChar : AddChar (ZMod d) ℂ)

omit [NeZero d] in
lemma two_mul_inv_two (hd : Odd d) : (2 : ZMod d) * 2⁻¹ = 1 := by
  have h : Nat.Coprime 2 d := Nat.coprime_two_left.2 hd
  have hu : IsUnit (2 : ZMod d) := by
    have := (ZMod.unitOfCoprime 2 h).isUnit
    rwa [ZMod.coe_unitOfCoprime, Nat.cast_ofNat] at this
  exact ZMod.mul_inv_of_unit _ hu

omit [NeZero d] in
lemma inv_two_mul_two (hd : Odd d) : (2 : ZMod d)⁻¹ * 2 = 1 := by
  rw [mul_comm]; exact two_mul_inv_two hd

lemma star_char (t : ZMod d) : star (ω t) = ω (-t) := by
  rw [ZMod.stdAddChar_apply, ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
  rfl

lemma char_mul_star (t : ZMod d) : ω t * star (ω t) = 1 := by
  rw [star_char, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]

lemma star_char_mul (t : ZMod d) : star (ω t) * ω t = 1 := by
  rw [mul_comm, char_mul_star]

lemma char_ne_zero (t : ZMod d) : ω t ≠ 0 := by
  intro h; have := char_mul_star t; rw [h, zero_mul] at this; exact zero_ne_one this

lemma char_eq_one_iff (t : ZMod d) : ω t = 1 ↔ t = 0 := by
  rw [← AddChar.map_zero_eq_one (ZMod.stdAddChar : AddChar (ZMod d) ℂ),
    ZMod.injective_stdAddChar.eq_iff]

lemma char_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod d) :
    ω (∑ i ∈ s, f i) = ∏ i ∈ s, ω (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

/-- Character orthogonality on `ℤ_dⁿ`: `Σ_p ω(p · y) = dⁿ [y = 0]`. -/
lemma sum_char_dot (y : Config d n) :
    ∑ p : Config d n, ω (p ⬝ᵥ y) = if y = 0 then (d : ℂ) ^ n else 0 := by
  have h1 : ∀ p : Config d n, ω (p ⬝ᵥ y) = ∏ i, ω (p i * y i) := by
    intro p; simp only [dotProduct, char_sum]
  simp_rw [h1]
  have h3 := (Finset.prod_univ_sum (fun _ : Fin n => (univ : Finset (ZMod d)))
    (fun i t => ω (t * y i))).symm
  rw [Fintype.piFinset_univ] at h3
  rw [h3]
  have h2 : ∀ i, ∑ t : ZMod d, ω (t * y i) = if y i = 0 then (d : ℂ) else 0 := by
    intro i
    rw [AddChar.sum_mulShift (y i) (ZMod.isPrimitive_stdAddChar d), ZMod.card]
    split_ifs <;> simp
  simp_rw [h2]
  rw [Finset.prod_ite_zero]
  by_cases hy : y = 0
  · subst hy; simp
  · have : ¬ ∀ i ∈ (univ : Finset (Fin n)), y i = 0 :=
      fun h => hy (funext fun i => h i (mem_univ i))
    simp only [this, hy, ite_false]

/-- The same with the dot product taken the other way round. -/
lemma sum_char_dot' (y : Config d n) :
    ∑ p : Config d n, ω (y ⬝ᵥ p) = if y = 0 then (d : ℂ) ^ n else 0 := by
  simp_rw [dotProduct_comm y]; exact sum_char_dot y

/-- Parseval for the Fourier transform on `ℤ_dⁿ`. -/
lemma parseval (h : Config d n → ℂ) :
    ∑ p : Config d n, (∑ x, ω (p ⬝ᵥ x) * h x) * star (∑ x, ω (p ⬝ᵥ x) * h x) =
      (d : ℂ) ^ n * ∑ x, h x * star (h x) := by
  have key : ∀ p : Config d n, (∑ x, ω (p ⬝ᵥ x) * h x) * star (∑ x, ω (p ⬝ᵥ x) * h x) =
      ∑ x, ∑ y, ω (p ⬝ᵥ (x - y)) * (h x * star (h y)) := by
    intro p
    rw [star_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [star_mul', star_char, dotProduct_sub, sub_eq_add_neg, AddChar.map_add_eq_mul]
    ring
  simp_rw [key]
  calc ∑ p : Config d n, ∑ x, ∑ y, ω (p ⬝ᵥ (x - y)) * (h x * star (h y))
      = ∑ x, ∑ y, (∑ p : Config d n, ω (p ⬝ᵥ (x - y))) * (h x * star (h y)) := by
        rw [Finset.sum_comm]; refine sum_congr rfl fun x _ => ?_
        rw [Finset.sum_comm]; refine sum_congr rfl fun y _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ x, (d : ℂ) ^ n * (h x * star (h x)) := by
        refine sum_congr rfl fun x _ => ?_
        simp_rw [sum_char_dot, sub_eq_zero, ite_mul, zero_mul]
        rw [Finset.sum_ite_eq]; simp
    _ = _ := by rw [Finset.mul_sum]

end DiscreteHudson
