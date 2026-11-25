/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/
module

public import DiscreteHudson.Weyl

/-!
# Sums over phase space

For odd `d`, with `‖ψ‖² = Σ_x |ψ(x)|²`:

* `inner_phasePoint_eq`: `⟨ψ|A(p, q)|ψ⟩ = Σ_ξ ω(p · ξ) ψ̄(q + ξ/2) ψ(q - ξ/2)`;
* `sum_inner_phasePoint`: `Σ_a ⟨ψ|A(a)|ψ⟩ = dⁿ ‖ψ‖²`;
* `sum_inner_phasePoint_sq`: `Σ_a |⟨ψ|A(a)|ψ⟩|² = dⁿ ‖ψ‖⁴`;
* `sum_inner_weyl_sq`: `Σ_v |⟨ψ|w(v)|ψ⟩|² = dⁿ ‖ψ‖⁴`.
-/

@[expose] public section

open Finset

namespace DiscreteHudson

variable {d n : ℕ} [NeZero d]

local notation "ω" => (ZMod.stdAddChar : AddChar (ZMod d) ℂ)

/-- `x ↦ 2(x - q)`, a bijection of configuration space for odd `d`. -/
def doubleEquiv (hd : Odd d) (q : Config d n) : Config d n ≃ Config d n where
  toFun x := (2 : ZMod d) • (x - q)
  invFun ξ := q + (2 : ZMod d)⁻¹ • ξ
  left_inv x := by simp only [smul_smul, inv_two_mul_two hd, one_smul, add_sub_cancel]
  right_inv ξ := by simp only [add_sub_cancel_left, smul_smul, two_mul_inv_two hd, one_smul]

/-- `q ↦ 2q - u`, a bijection of configuration space for odd `d`. -/
def reflEquiv (hd : Odd d) (u : Config d n) : Config d n ≃ Config d n where
  toFun q := (2 : ZMod d) • q - u
  invFun y := (2 : ZMod d)⁻¹ • (y + u)
  left_inv q := by simp only [sub_add_cancel, smul_smul, inv_two_mul_two hd, one_smul]
  right_inv y := by simp only [smul_smul, two_mul_inv_two hd, one_smul, add_sub_cancel_right]

lemma inner_phasePoint_eq (hd : Odd d) (ψ : Config d n → ℂ) (p q : Config d n) :
    ∑ x, star (ψ x) * phasePoint (p, q) ψ x =
      ∑ ξ, ω (p ⬝ᵥ ξ) * (star (ψ (q + (2 : ZMod d)⁻¹ • ξ)) * ψ (q - (2 : ZMod d)⁻¹ • ξ)) := by
  refine Fintype.sum_equiv (doubleEquiv hd q) _ _ (fun x => ?_)
  simp only [doubleEquiv, Equiv.coe_fn_mk, smul_smul, inv_two_mul_two hd, one_smul,
    add_sub_cancel, phasePoint_apply hd, dotProduct_smul, smul_eq_mul]
  rw [show q - (x - q) = (2 : ZMod d) • q - x by rw [two_smul]; abel]
  ring

lemma sum_inner_phasePoint (hd : Odd d) (ψ : Config d n → ℂ) :
    ∑ a : PhaseSpace d n, ∑ x, star (ψ x) * phasePoint a ψ x =
      (d : ℂ) ^ n * ∑ x, star (ψ x) * ψ x := by
  rw [Fintype.sum_prod_type]
  simp_rw [inner_phasePoint_eq hd]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (γ := Config d n) (s := univ) (t := univ)
    (f := fun p ξ => ω (p ⬝ᵥ ξ) * _), ← Finset.sum_mul, sum_char_dot, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ]
  simp only [↓reduceIte, smul_zero, add_zero, sub_zero, Finset.mul_sum]

lemma sum_mul_star_shift (hd : Odd d) (ψ : Config d n → ℂ) :
    ∑ q : Config d n, ∑ ξ, (star (ψ (q + (2 : ZMod d)⁻¹ • ξ)) * ψ (q - (2 : ZMod d)⁻¹ • ξ)) *
        star (star (ψ (q + (2 : ZMod d)⁻¹ • ξ)) * ψ (q - (2 : ZMod d)⁻¹ • ξ)) =
      (∑ x, star (ψ x) * ψ x) * ∑ x, star (ψ x) * ψ x := by
  have h1 : ∀ q : Config d n,
      ∑ ξ, (star (ψ (q + (2 : ZMod d)⁻¹ • ξ)) * ψ (q - (2 : ZMod d)⁻¹ • ξ)) *
        star (star (ψ (q + (2 : ZMod d)⁻¹ • ξ)) * ψ (q - (2 : ZMod d)⁻¹ • ξ)) =
      ∑ u, (star (ψ u) * ψ u) * (star (ψ ((2 : ZMod d) • q - u)) * ψ ((2 : ZMod d) • q - u)) := by
    intro q
    refine Fintype.sum_equiv ((doubleEquiv hd q).symm) _ _ (fun ξ => ?_)
    simp only [doubleEquiv, Equiv.coe_fn_symm_mk, star_mul', star_star]
    rw [show (2 : ZMod d) • q - (q + (2 : ZMod d)⁻¹ • ξ) = q - (2 : ZMod d)⁻¹ • ξ by
      rw [two_smul]; abel]
    ring
  simp_rw [h1]
  rw [Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.mul_sum]
  congr 1
  exact Fintype.sum_equiv (reflEquiv hd u) _ _ (fun q => rfl)

lemma sum_inner_phasePoint_sq (hd : Odd d) (ψ : Config d n → ℂ) :
    ∑ a : PhaseSpace d n, (∑ x, star (ψ x) * phasePoint a ψ x) *
        star (∑ x, star (ψ x) * phasePoint a ψ x) =
      (d : ℂ) ^ n * ((∑ x, star (ψ x) * ψ x) * ∑ x, star (ψ x) * ψ x) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [inner_phasePoint_eq hd, parseval, ← Finset.mul_sum]
  rw [sum_mul_star_shift hd]

lemma inner_weyl_eq (ψ : Config d n → ℂ) (p q : Config d n) :
    ∑ x, star (ψ x) * weyl (p, q) ψ x =
      ω (-((2 : ZMod d)⁻¹ * (p ⬝ᵥ q))) * ∑ x, ω (p ⬝ᵥ x) * (star (ψ x) * ψ (x - q)) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [weyl, AddChar.map_add_eq_mul]
  ring

lemma sum_inner_weyl_sq (ψ : Config d n → ℂ) :
    ∑ v : PhaseSpace d n, (∑ x, star (ψ x) * weyl v ψ x) * star (∑ x, star (ψ x) * weyl v ψ x) =
      (d : ℂ) ^ n * ((∑ x, star (ψ x) * ψ x) * ∑ x, star (ψ x) * ψ x) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  have h1 : ∀ q p : Config d n,
      (∑ x, star (ψ x) * weyl (p, q) ψ x) * star (∑ x, star (ψ x) * weyl (p, q) ψ x) =
      (∑ x, ω (p ⬝ᵥ x) * (star (ψ x) * ψ (x - q))) *
        star (∑ x, ω (p ⬝ᵥ x) * (star (ψ x) * ψ (x - q))) := by
    intro q p
    rw [inner_weyl_eq, star_mul']
    calc ω _ * (∑ x, ω (p ⬝ᵥ x) * (star (ψ x) * ψ (x - q))) *
          (star (ω _) * star (∑ x, ω (p ⬝ᵥ x) * (star (ψ x) * ψ (x - q))))
        = (ω _ * star (ω _)) * ((∑ x, ω (p ⬝ᵥ x) * (star (ψ x) * ψ (x - q))) *
          star (∑ x, ω (p ⬝ᵥ x) * (star (ψ x) * ψ (x - q)))) := by ring
      _ = _ := by rw [char_mul_star, one_mul]
  simp_rw [h1, parseval, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h2 : ∀ q, (star (ψ x) * ψ (x - q)) * star (star (ψ x) * ψ (x - q)) =
      (star (ψ x) * ψ x) * (star (ψ (x - q)) * ψ (x - q)) := by
    intro q; simp only [star_mul', star_star]; ring
  simp_rw [h2, ← Finset.mul_sum]
  congr 1
  exact Fintype.sum_equiv (Equiv.subLeft x) _ _ (fun q => rfl)

end DiscreteHudson
