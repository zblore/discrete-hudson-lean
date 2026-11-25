/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import DiscreteHudson

/-!
# Controls

Both sides of `discrete_hudson` take both truth values, so the theorem is not vacuous:

* `ket0_isStabilizerState`: the basis vector `|0⋯0⟩` is a stabilizer state, for every `d` and `n`
  (`M = {(p, 0)}`), so its Wigner function is non-negative (`ket0_wigner_nonneg`).
* `norrell_wigner_neg`: for one qutrit, the Norrell state `|1⟩ - |2⟩` has `W(0, 0) = -2/3 < 0` (`-1/3` once normalised),
  so it is not a stabilizer state (`norrell_not_isStabilizerState`).

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
  (discrete_hudson hd _ (ket0_ne_zero d n)).2 (ket0_isStabilizerState d n) a

/-- The Norrell state `|1⟩ - |2⟩` of one qutrit (unnormalised). -/
noncomputable def norrell : Config 3 1 → ℂ := fun x => ![0, 1, -1] (x 0)

theorem norrell_wigner_neg : (wigner norrell 0).re < 0 := by
  have hd : Odd 3 := by decide
  have h1 : ∀ x : Config 3 1, phasePoint 0 norrell x = norrell (-x) := by
    intro x; rw [phasePoint_apply hd]; simp
  set g : ZMod 3 → ℂ := fun y => star (![(0 : ℂ), 1, -1] y) * ![(0 : ℂ), 1, -1] (-y) with hg
  have h2 : ∑ x : Config 3 1, star (norrell x) * phasePoint 0 norrell x = ∑ y : ZMod 3, g y := by
    simp_rw [h1]
    exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) (ZMod 3)) _ _ (fun x => rfl)
  have h3 : ∑ y : ZMod 3, g y = g 0 + g 1 + g 2 := Fin.sum_univ_three g
  have g0 : g 0 = 0 := by change star (0 : ℂ) * (0 : ℂ) = 0; simp
  have g1 : g 1 = -1 := by change star (1 : ℂ) * (-1 : ℂ) = -1; simp
  have g2 : g 2 = -1 := by change star (-1 : ℂ) * (1 : ℂ) = -1; simp
  rw [wigner, h2, h3, g0, g1, g2]
  norm_num

theorem norrell_not_isStabilizerState : ¬ IsStabilizerState norrell := by
  intro h
  have hne : norrell ≠ 0 := fun h0 => by
    have := congrFun h0 (fun _ => 1); simp [norrell] at this
  have := (discrete_hudson (by decide) norrell hne).2 h 0
  have := (Complex.le_def.1 this).1
  simp only [Complex.zero_re] at this
  linarith [norrell_wigner_neg]

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
info: 'DiscreteHudson.Control.norrell_wigner_neg' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DiscreteHudson.Control.norrell_wigner_neg

/--
info: 'DiscreteHudson.Control.norrell_not_isStabilizerState' depends on axioms:
  [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms DiscreteHudson.Control.norrell_not_isStabilizerState

end DiscreteHudson.Control

/-! ### The canary, last -/

/-- warning: declaration uses `sorry` -/
#guard_msgs in
theorem canary : False := sorry

/-- info: 'canary' depends on axioms: [sorryAx] -/
#guard_msgs in
#print axioms canary
