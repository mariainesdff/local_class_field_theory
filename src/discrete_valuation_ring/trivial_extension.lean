/-
Copyright (c) 2023 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import discrete_valuation_ring.extensions

open add_subgroup discrete_valuation polynomial valuation with_zero
open_locale discrete_valuation

namespace discrete_valuation.extension

variables {K : Type*} [field K] [hv : valued K ℤₘ₀] [is_discrete hv.v] [complete_space K]

include hv

lemma trivial_pow_extension_on_units_eq_valuation (x : Kˣ):
  pow_extension_on_units K K x = unzero (valuation.unit_ne_zero hv.v x) :=
begin
  rw [pow_extension_on_units_apply],
  congr,
  simp only [finite_dimensional.finrank_self, minpoly.eq_X_sub_C',units.val_eq_coe, coeff_sub, 
    coeff_X_zero, coeff_C_zero, zero_sub, valuation.map_neg, nat_degree_X_sub_C, nat.div_self, 
    nat.lt_one_iff, pow_one],
end

variables (K)

lemma trivial_exp_extension_on_units_eq_one : exp_extension_on_units K K = 1 :=
begin
  have h : zmultiples (exp_extension_on_units K K : ℤ) = ⊤,
  { rw [zmultiples_eq_closure, ← exp_extension_on_units_generates_range', map_eq_top_iff],
    apply subgroup.map_top_of_surjective,
    intros z,
    have hz : ∃ (u : Kˣ), valued.v (u : K) = (z : ℤₘ₀),
    { have hd : is_discrete hv.v := infer_instance,
      obtain ⟨k, hk⟩ := hd.surj z,
      have hk0 : k ≠ 0, 
      { rw [ne.def, ← valuation.zero_iff hv.v, hk], exact coe_ne_zero },
      exact ⟨is_unit.unit (is_unit_iff_ne_zero.mpr hk0), hk⟩,},
    obtain ⟨u, hu⟩ := hz,
    use u,
    rw [trivial_pow_extension_on_units_eq_valuation, ← with_zero.coe_inj, ← hu, coe_unzero] },
  rw [← int.coe_nat_inj', nat.cast_one],
  apply int.eq_one_of_dvd_one (nat.cast_nonneg _),
  rw [← int.mem_zmultiples_iff, h],
  exact add_subgroup.mem_top _,
end

lemma trivial_extension_eq_valuation : extension K K = hv.v :=
begin
  ext x,
  rw extension.apply,
  split_ifs with hx hx,
  { rw [hx, valuation.map_zero] },
  { set u : Kˣ := (is_unit_iff_ne_zero.mpr hx).unit, 
    rw ← zpow_eq_pow,
    convert (exists_mul_exp_extension_on_units K u).some_spec,
    { simp_rw [zpow_eq_pow, trivial_exp_extension_on_units_eq_one, pow_one] },
    { simp only [finite_dimensional.finrank_self, minpoly.eq_X_sub_C', is_unit.unit_spec, 
        coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, valuation.map_neg, nat_degree_X_sub_C,
        nat.div_self, nat.lt_one_iff, pow_one] }}
end


end discrete_valuation.extension