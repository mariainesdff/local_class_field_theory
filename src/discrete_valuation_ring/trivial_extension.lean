/-
Copyright (c) 2023 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import discrete_valuation_ring.extensions

open discrete_valuation polynomial valuation
open_locale discrete_valuation

namespace discrete_valuation.extension

variables {K : Type*} [field K] [hv : valued K ℤₘ₀] [is_discrete hv.v] [complete_space K]

include hv

lemma trivial_pow_extension_on_units_eq_valuation (x : Kˣ):
  pow_extension_on_units K K x = with_zero.unzero (valuation.unit_ne_zero hv.v x) :=
begin
  rw [pow_extension_on_units_apply],
  congr,
  simp only [finite_dimensional.finrank_self, minpoly.eq_X_sub_C',units.val_eq_coe, coeff_sub, 
    coeff_X_zero, coeff_C_zero, zero_sub, valuation.map_neg, nat_degree_X_sub_C, nat.div_self, 
    nat.lt_one_iff, pow_one],
end

lemma trivial_exp_extension_on_units_eq_one : exp_extension_on_units K K = 1 :=
begin
  
  sorry
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