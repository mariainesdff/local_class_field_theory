/-
Copyright (c) 2023 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import ring_theory.valuation.basic
import data.real.nnreal


noncomputable theory

open_locale discrete_valuation nnreal

open multiplicative with_zero

namespace with_zero

theorem one_lt_zpow' {α : Type*} [linear_ordered_comm_group_with_zero α] {a : α} 
  (ha : 1 < a) {k : ℤ} (hk : 0 < k) : 1 < a ^ k :=
begin
  lift k to ℕ using int.le_of_lt hk,
  rw zpow_coe_nat,
  exact one_lt_pow' ha (int.coe_nat_pos.mp hk).ne',
end

theorem mul_lt_mul_right₀ {α : Type*} {a b c : α} [linear_ordered_comm_group_with_zero α] 
  (hc : 0 < c) : a * c < b * c ↔ a < b :=
begin
  rw [mul_comm a, mul_comm b],
  exact ⟨λ h, lt_of_mul_lt_mul_of_le₀ h hc (le_refl _), 
    λ h, mul_lt_mul_of_lt_of_le₀ (le_refl _) (ne_of_gt hc) h⟩,
end

theorem one_lt_div' {α : Type*} [linear_ordered_comm_group_with_zero α] (a : α)
  {b : α} (hb : b ≠ 0) : 1 < a / b ↔ b < a :=
by rw [← mul_lt_mul_right₀ (zero_lt_iff.mpr hb), one_mul, div_eq_mul_inv, inv_mul_cancel_right₀ hb]

open_locale discrete_valuation 

-- TODO: generalize these

theorem strict_mono_on_zpow {n : ℤ} (hn : 0 < n) :
  strict_mono_on (λ (x : ℤₘ₀), x ^ n) (set.Ioi 0) := λ a ha b hb hab, 
begin 
  simp only [set.mem_Ioi] at ha hb,
  have ha0 : a ≠ 0 := ne_of_gt ha, 
  have han : a^n ≠ 0,
  { rw with_zero.ne_zero_iff_exists at ha0 ⊢,
    obtain ⟨x, hx⟩ := ha0,
    exact ⟨x^n,by rw [← hx, with_zero.coe_zpow]⟩ },
  simp only [← one_lt_div' _ han, ← div_zpow],
  exact one_lt_zpow' ((one_lt_div' _ ha0).mpr hab) hn
end

theorem zpow_left_inj_on {n : ℤ} (hn : n ≠ 0) : 
  set.inj_on (λ (_x : ℤₘ₀), _x ^ n) (set.Ioi 0) :=
begin
  cases hn.symm.lt_or_lt,
  { exact (strict_mono_on_zpow h).inj_on },
  { refine λ a ha b hb (hab : a ^ n = b ^ n), (strict_mono_on_zpow (neg_pos.mpr h)).inj_on ha hb _,
    simp only [zpow_neg, zpow_neg, hab] }
end

theorem zpow_left_inj {n : ℤ} {a b : ℤₘ₀} (ha : a ≠ 0) (hb : b ≠ 0) (hn : n ≠ 0) :
  a ^ n = b ^ n ↔ a = b :=
set.inj_on.eq_iff (zpow_left_inj_on hn) (set.mem_Ioi.mpr (zero_lt_iff.mpr ha)) 
    (set.mem_Ioi.mpr (zero_lt_iff.mpr hb))
/- (zpow_left_injective hn).eq_iff -/

end with_zero

def with_zero_mult_int_to_nnreal_def (e : nnreal) : ℤₘ₀ → ℝ≥0 := 
λ x, if hx : x = 0 then 0 else e^(multiplicative.to_add (with_zero.unzero hx))

open with_zero

def with_zero_mult_int_to_nnreal {e : nnreal} (he : e ≠ 0)  : ℤₘ₀ →*₀ ℝ≥0 := 
{ to_fun    := with_zero_mult_int_to_nnreal_def e,
  map_zero' := by { simp only [with_zero_mult_int_to_nnreal_def], rw dif_pos, refl },
  map_one'  := begin
    simp only [with_zero_mult_int_to_nnreal_def], rw dif_neg,
    { simp only [unzero_coe, to_add_one, zpow_zero] },
    { exact ne_zero.ne 1 },
  end,
  map_mul'  := λ x y, begin
    simp only [with_zero_mult_int_to_nnreal_def],
    by_cases hxy : x * y = 0,
    { cases (zero_eq_mul.mp (eq.symm hxy)) with hx hy, --either x = 0 or y = 0
      { rw [dif_pos hxy, dif_pos hx, zero_mul] },
      { rw [dif_pos hxy, dif_pos hy, mul_zero] },},
    { cases (mul_ne_zero_iff.mp hxy) with hx hy, --  x ≠ 0 and y ≠ 0
      rw [dif_neg hxy, dif_neg hx, dif_neg hy, ← zpow_add' (or.inl he)], 
      apply congr_arg,
      rw ← to_add_mul,
      apply congr_arg,
      rw [← with_zero.coe_inj, with_zero.coe_mul, coe_unzero hx,coe_unzero hy, coe_unzero hxy] },
  end }

lemma with_zero_mult_int_to_nnreal_strict_mono {e : nnreal} (he : 1 < e) : 
  strict_mono (with_zero_mult_int_to_nnreal (ne_zero_of_lt he))  := 
begin
  intros x y hxy,
  simp only [with_zero_mult_int_to_nnreal, with_zero_mult_int_to_nnreal_def, 
    monoid_with_zero_hom.coe_mk],
  split_ifs with hx hy hy,
  { simp only [hy, not_lt_zero'] at hxy, exfalso, exact hxy },
  { apply nnreal.zpow_pos (ne_zero_of_lt he) },
  { simp only [hy, not_lt_zero'] at hxy, exfalso, exact hxy },
  { rw [zpow_lt_iff_lt he, multiplicative.to_add_lt, ← with_zero.coe_lt_coe,
      with_zero.coe_unzero hx, with_zero.coe_unzero hy],
    exact hxy }
end