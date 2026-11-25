/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import DiscreteHudson

/-!
# Controls

Both sides of `discrete_hudson` take both truth values, so the theorem is not vacuous, and it is
exercised at a composite dimension:

* `ket0_isStabilizerState`: the basis vector `|0⋯0⟩` is a stabilizer state, for every `d` and `n`
  (`M = {(p, 0)}`), so its Wigner function is non-negative (`ket0_wigner_nonneg`).
* `strange_wigner_neg`: for one qutrit, the Strange state `|1⟩ - |2⟩` (Veitch, Mousavian,
  Gottesman and Emerson, arXiv:1307.7171) has `W(0, 0) = -2/3 < 0` (`-1/3` once normalised), so it
  is not a stabilizer state (`strange_not_isStabilizerState`).
* `nine_isStabilizerState`: for `d = 9`, the vector `|0⟩ + |3⟩ + |6⟩` is a stabilizer state for
  `M = 3ℤ₉ × 3ℤ₉`, a subgroup that is not a subspace over a field; so its Wigner function is
  non-negative (`nine_wigner_nonneg`).

The axiom audit would catch a `sorry`: the canary comes last.
-/

@[expose] public section

open DiscreteHudson
open scoped ComplexOrder

namespace DiscreteHudson.Control

/-- The basis vector `|0⋯0⟩`. -/
noncomputable def ket0 (d n : ℕ) : Config d n → ℂ := fun x => if x = 0 then 1 else 0

theorem ket0_ne_zero (d n : ℕ) [NeZero d] : ket0 d n ≠ 0 := fun h => by
  have := congrFun h 0; simp [ket0] at this

theorem ket0_isStabilizerState (d n : ℕ) [NeZero d] : IsStabilizerState (ket0 d n) := by
  refine ⟨(⊤ : AddSubgroup (Config d n)).prod ⊥, ?_, ?_, ?_⟩
  · intro u hu v hv
    rw [AddSubgroup.mem_prod, AddSubgroup.mem_bot] at hu hv
    simp [symp, hu.2, hv.2]
  · rw [Nat.card_congr (AddSubgroup.prodEquiv _ _).toEquiv, Nat.card_prod, AddSubgroup.card_top,
      AddSubgroup.card_bot, mul_one, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card,
      Fintype.card_fin]
  · intro m hm
    rw [AddSubgroup.mem_prod, AddSubgroup.mem_bot] at hm
    refine ⟨1, funext fun x => ?_⟩
    simp only [weyl, hm.2, dotProduct_zero, mul_zero, neg_zero, zero_add, sub_zero,
      Pi.smul_apply, smul_eq_mul, one_mul, ket0]
    split_ifs with hx
    · rw [hx, dotProduct_zero, AddChar.map_zero_eq_one, mul_one]
    · rw [mul_zero]

theorem ket0_wigner_nonneg {d : ℕ} [NeZero d] (hd : Odd d) (n : ℕ) (a : PhaseSpace d n) :
    0 ≤ wigner (ket0 d n) a :=
  (discrete_hudson hd _).2 (ket0_isStabilizerState d n) a

/-- The Strange state `|1⟩ - |2⟩` of one qutrit (unnormalised). -/
noncomputable def strange : Config 3 1 → ℂ := fun x => ![0, 1, -1] (x 0)

theorem strange_wigner_neg : (wigner strange 0).re < 0 := by
  have hd : Odd 3 := by decide
  have h1 : ∀ x : Config 3 1, phasePoint 0 strange x = strange (-x) := by
    intro x; rw [phasePoint_apply hd]; simp
  set g : ZMod 3 → ℂ := fun y => star (![(0 : ℂ), 1, -1] y) * ![(0 : ℂ), 1, -1] (-y) with hg
  have h2 : ∑ x : Config 3 1, star (strange x) * phasePoint 0 strange x = ∑ y : ZMod 3, g y := by
    simp_rw [h1]
    exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) (ZMod 3)) _ _ (fun x => rfl)
  have h3 : ∑ y : ZMod 3, g y = g 0 + g 1 + g 2 := Fin.sum_univ_three g
  have g0 : g 0 = 0 := by change star (0 : ℂ) * (0 : ℂ) = 0; simp
  have g1 : g 1 = -1 := by change star (1 : ℂ) * (-1 : ℂ) = -1; simp
  have g2 : g 2 = -1 := by change star (-1 : ℂ) * (1 : ℂ) = -1; simp
  rw [wigner, h2, h3, g0, g1, g2]
  norm_num

theorem strange_not_isStabilizerState : ¬ IsStabilizerState strange := by
  intro h
  have := (discrete_hudson (by decide) strange).2 h 0
  have := (Complex.le_def.1 this).1
  simp only [Complex.zero_re] at this
  linarith [strange_wigner_neg]


/-! ### A composite dimension -/

/-- `g = 3`, as a vector of one qudit of dimension nine. -/
def g9 : Config 9 1 := fun _ => 3

lemma three_smul_g9 : (3 : ℕ) • g9 = 0 := by
  funext i; simp only [g9, Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]; decide

lemma g9_ne_zero : g9 ≠ 0 := fun h => by
  have := congrFun h 0; simp only [g9, Pi.zero_apply] at this; exact absurd this (by decide)

lemma g9_dot_self : g9 ⬝ᵥ g9 = 0 := by
  simp only [g9, dotProduct, Fin.sum_univ_one]; decide

lemma g9_dot (k l : ℤ) : (k • g9) ⬝ᵥ (l • g9) = 0 := by
  rw [smul_dotProduct, dotProduct_smul, g9_dot_self, smul_zero, smul_zero]

/-- `M = 3ℤ₉ × 3ℤ₉`. -/
def M9 : AddSubgroup (PhaseSpace 9 1) :=
  (AddSubgroup.zmultiples g9).prod (AddSubgroup.zmultiples g9)

/-- `|0⟩ + |3⟩ + |6⟩`: the indicator of `3ℤ₉`. -/
noncomputable def nine : Config 9 1 → ℂ := fun x => if (3 : ℕ) • x = 0 then 1 else 0

theorem nine_isStabilizerState : IsStabilizerState nine := by
  have hord : addOrderOf g9 = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact addOrderOf_eq_prime three_smul_g9 g9_ne_zero
  refine ⟨M9, ?_, ?_, ?_⟩
  · rintro u hu v hv
    rw [M9, AddSubgroup.mem_prod, AddSubgroup.mem_zmultiples_iff,
      AddSubgroup.mem_zmultiples_iff] at hu hv
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hu
    obtain ⟨⟨c, hc⟩, ⟨e, he⟩⟩ := hv
    simp only [symp, ← ha, ← hb, ← hc, ← he, g9_dot, sub_zero]
  · rw [M9, Nat.card_congr (AddSubgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
      Nat.card_zmultiples, hord]
    norm_num
  · intro m hm
    rw [M9, AddSubgroup.mem_prod, AddSubgroup.mem_zmultiples_iff,
      AddSubgroup.mem_zmultiples_iff] at hm
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hm
    refine ⟨1, funext fun x => ?_⟩
    simp only [weyl, ← ha, ← hb, g9_dot, mul_zero, neg_zero, zero_add, Pi.smul_apply,
      smul_eq_mul, one_mul, nine]
    have h3 : (3 : ℕ) • (b • g9) = 0 := by rw [smul_comm, three_smul_g9, smul_zero]
    have hshift : (3 : ℕ) • (x - b • g9) = (3 : ℕ) • x := by rw [smul_sub, h3, sub_zero]
    rw [hshift]
    split_ifs with hx
    · have hdot : (a • g9) ⬝ᵥ x = 0 := by
        have hx0 := congrFun hx 0
        simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul] at hx0
        have hgx : g9 ⬝ᵥ x = 0 := by
          simp only [g9, dotProduct, Fin.sum_univ_one]; exact_mod_cast hx0
        rw [smul_dotProduct, hgx, smul_zero]
      rw [hdot, AddChar.map_zero_eq_one, mul_one]
    · rw [mul_zero]

theorem nine_wigner_nonneg (a : PhaseSpace 9 1) : 0 ≤ wigner nine a :=
  (discrete_hudson (by decide) nine).2 nine_isStabilizerState a

/-! ### Axioms of the controls -/

/--
info: 'DiscreteHudson.Control.ket0_isStabilizerState' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DiscreteHudson.Control.ket0_isStabilizerState

/--
info: 'DiscreteHudson.Control.ket0_wigner_nonneg' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DiscreteHudson.Control.ket0_wigner_nonneg

/--
info: 'DiscreteHudson.Control.strange_wigner_neg' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DiscreteHudson.Control.strange_wigner_neg

/--
info: 'DiscreteHudson.Control.strange_not_isStabilizerState' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DiscreteHudson.Control.strange_not_isStabilizerState

/--
info: 'DiscreteHudson.Control.nine_isStabilizerState' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DiscreteHudson.Control.nine_isStabilizerState

/--
info: 'DiscreteHudson.Control.nine_wigner_nonneg' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DiscreteHudson.Control.nine_wigner_nonneg

end DiscreteHudson.Control

/-! ### The canary, last -/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem canary : False := sorry

/-- info: 'canary' depends on axioms: [sorryAx] -/
#guard_msgs in
#print axioms canary
