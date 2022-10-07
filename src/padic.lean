/-
Copyright (c) 2022 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import number_theory.padics.padic_integers

noncomputable theory

open function
open_locale big_operators

namespace padic_int

variables {p : ℕ} [fact(nat.prime p)]

lemma coe_eq_zero (x : ℤ_[p]) : (x : ℚ_[p]) = 0  ↔ x = 0 :=
⟨λ h, by {rw ← padic_int.coe_zero at h, exact subtype.coe_inj.mp h},
    λ h, by {rw h, exact padic_int.coe_zero}⟩

/-- `ℤ_[p]` with its usual ring structure is not a field. -/
lemma not_is_field (p : ℕ) [hp : fact(nat.prime p)] : ¬ is_field ℤ_[p] :=
begin
  rw ring.not_is_field_iff_exists_ideal_bot_lt_and_lt_top,
  use ideal.span {(p : ℤ_[p])},
  split,
  { rw [bot_lt_iff_ne_bot, ne.def, ideal.span_singleton_eq_bot, nat.cast_eq_zero],
    exact hp.1.ne_zero },
  { rw [lt_top_iff_ne_top, ne.def, ideal.eq_top_iff_one, ideal.mem_span_singleton,
      ← padic_int.norm_lt_one_iff_dvd, norm_one, not_lt], }
end

end padic_int

-- For instances/lemmas about ℚₚ and ℤₚ
namespace padic

variables {p : ℕ} [fact(nat.prime p)]

instance algebra : algebra ℤ_[p] ℚ_[p] := ring_hom.to_algebra (padic_int.coe.ring_hom)

lemma algebra_map_def : algebra_map ℤ_[p] ℚ_[p] =  padic_int.coe.ring_hom := rfl
lemma algebra_map_apply (x : ℤ_[p]) : algebra_map ℤ_[p] ℚ_[p] x = x := rfl

lemma norm_le_one_iff_val_nonneg (x : ℚ_[p]) : ∥ x ∥ ≤ 1 ↔ 0 ≤ x.valuation := 
begin
  by_cases hx : x = 0,
  { simp only [hx, norm_zero, padic.valuation_zero, zero_le_one, le_refl], },
  { rw [padic.norm_eq_pow_val hx, ← zpow_zero (p : ℝ), zpow_le_iff_le 
      (nat.one_lt_cast.mpr (nat.prime.one_lt' p).1), right.neg_nonpos_iff], 
    apply_instance, }
end

instance is_fraction_ring : is_fraction_ring ℤ_[p] ℚ_[p] :=
{ map_units := 
  begin
    rintros ⟨x, hx⟩,
    rw [set_like.coe_mk, algebra_map_apply, is_unit_iff_ne_zero, ne.def,
      padic_int.coe_eq_zero],
    exact mem_non_zero_divisors_iff_ne_zero.mp hx,
  end,
  surj      := λ x,
  begin
    by_cases hx : ∥ x ∥ ≤ 1,
    { use (⟨x, hx⟩, 1),
      rw [submonoid.coe_one, map_one, mul_one],
      refl, },
    { set n := int.to_nat(- x.valuation) with hn,
      have hn_coe : (n : ℤ) = -x.valuation,
      { rw [hn, int.to_nat_of_nonneg],
        rw right.nonneg_neg_iff,
        rw norm_le_one_iff_val_nonneg at hx,
        exact le_of_lt (not_le.mp hx), },
      set a := x * p^n with ha,
      have ha_norm : ∥ a ∥ = 1,
      { have hx : x ≠ 0,
        { intro h0,
          rw [h0, norm_zero] at hx,
          exact hx (zero_le_one) },
        rw [ha, norm_mul, ← zpow_coe_nat, padic_norm_e.norm_p_pow, norm_eq_pow_val hx,
          ← zpow_add' , hn_coe, neg_neg, add_left_neg, zpow_zero],
        exact or.inl (nat.cast_ne_zero.mpr (ne_zero.ne p)) },
      set b := (p^n : ℤ_[p]) with hb,
      have hb_mem : b ∈ non_zero_divisors ℤ_[p],
      { exact mem_non_zero_divisors_iff_ne_zero.mpr (ne_zero.ne _) },
      use (⟨a, le_of_eq ha_norm⟩, ⟨b, hb_mem⟩),
      simp only [set_like.coe_mk, map_pow, map_nat_cast, algebra_map_apply,
        padic_int.coe_pow, padic_int.coe_nat_cast, subtype.coe_mk] }
  end,
  eq_iff_exists := λ x y,
  begin
    rw [algebra_map_apply, algebra_map_apply, subtype.coe_inj],
    refine ⟨λ h, _, _⟩,
    { use 1,
      simp only [submonoid.coe_one, mul_one],
      exact h },
    { rintro ⟨⟨c, hc⟩, h⟩,
      exact (mul_eq_mul_right_iff.mp h).resolve_right (mem_non_zero_divisors_iff_ne_zero.mp hc) }
  end }

end padic