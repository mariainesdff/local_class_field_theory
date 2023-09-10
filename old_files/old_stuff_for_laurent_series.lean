import for_mathlib.discrete_uniformity
import for_mathlib.power_series
import for_mathlib.polynomial
import algebra.order.hom.monoid
import ring_theory.dedekind_domain.adic_valuation
import ring_theory.dedekind_domain.ideal
import ring_theory.laurent_series
import ring_theory.power_series.well_known

#exit

noncomputable theory

namespace polynomial

variables {K : Type*} [field K]

open ratfunc power_series

lemma coe_coe (P : polynomial K) : (P : laurent_series K) = (↑P : ratfunc K) :=
  by { erw [ratfunc.coe_def, ratfunc.coe_alg_hom, lift_alg_hom_apply, ratfunc.num_algebra_map,
    ratfunc.denom_algebra_map P, map_one, div_one], refl}

lemma coe_ne_zero {f : polynomial K} : f ≠ 0 → (↑f : (power_series K)) ≠ 0 :=
by simp only [ne.def, coe_eq_zero_iff, imp_self]

end polynomial

namespace hahn_series

lemma single_pow {R : Type*} [ring R] (n : ℕ) : (hahn_series.single (n : ℤ) (1 : R)) =
  (hahn_series.single (1 : ℤ) 1) ^ n :=
begin
induction n with n h_ind,
    { simp only [nat.nat_zero_eq_zero, int.of_nat_eq_coe, zmod.nat_cast_self, zpow_zero],
     refl, },
    { rw [← int.coe_nat_add_one_out, ← one_mul (1 : R), ← hahn_series.single_mul_single, h_ind,
      pow_succ', one_mul (1 : R)]},
end

variables {K : Type*} [field K]

lemma single_inv (d : ℤ) (α : K) (hα : α ≠ 0) : (hahn_series.single (d : ℤ) (α : K))⁻¹ 
  = hahn_series.single (-d) (α⁻¹ : K) :=
by {rw [inv_eq_of_mul_eq_one_left], simpa only [hahn_series.single_mul_single, 
  add_left_neg, inv_mul_cancel hα]}

lemma single_zpow (n : ℤ) : (hahn_series.single (n : ℤ) (1 : K)) =
  (hahn_series.single (1 : ℤ) 1) ^ n :=
begin
  induction n with n_pos n_neg,
  { apply single_pow },
  { rw [int.neg_succ_of_nat_coe, int.coe_nat_add, nat.cast_one, ← inv_one,
    ← single_inv ((n_neg + 1) : ℤ) (1 : K) one_ne_zero, zpow_neg, ← nat.cast_one, ← int.coe_nat_add,
    algebra_map.coe_one, inv_inj, zpow_coe_nat, single_pow, inv_one] },
end

end hahn_series

namespace is_dedekind_domain.height_one_spectrum

lemma int_valuation_apply {R : Type*} [comm_ring R] [is_domain R] [is_dedekind_domain R] 
  (v : is_dedekind_domain.height_one_spectrum R) {r : R} :
  int_valuation v r = int_valuation_def v r := refl _

end is_dedekind_domain.height_one_spectrum
