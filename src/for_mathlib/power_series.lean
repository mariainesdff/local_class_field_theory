import field_theory.finite.galois_field
import ring_theory.power_series.basic
import ring_theory.valuation.valuation_subring
import for_mathlib.discrete_uniformity
import for_mathlib.polynomial
import algebra.order.hom.monoid
import ring_theory.laurent_series
import ring_theory.power_series.well_known

/-!
# Generalities on power series
In this file we gather some general results concerning power series. 

## Main Definitions
* Given a  power series `f`, we define `divided_by_X_pow f` to be the power series obtained by
dividing `f` bythe largest power of `X` occurring in `f`, namely `f.order` (this is also equal to
its `X`-adic valuation, up to some type-theoretical difference). 

## Main Results
We obtain instances of Dedekind domain and of normalization monoid on the power series with
coefficients in a field. 
* The definition `residue_field_of_power_series` is the ring isomorphism between the residue field
of the ring of power series valued in a field `K` and `K` itself.

In the final section, we prove 
* `single_pow`
* `single_inv`
* `single_zpow`
relating the powers and the inverse of the Hahn series `single 1 1` with the Hahn series 
`single n 1` for `n : ℤ`.
-/

namespace power_series

open_locale discrete_valuation

noncomputable theory

lemma coeff_zero_eq_eval {K : Type*} [semiring K] (f : power_series K) :
  (power_series.coeff K 0) f = f 0 :=
by simp only [power_series.coeff, mv_power_series.coeff, linear_map.coe_proj,
  function.eval_apply, finsupp.single_zero]

lemma order_zero_of_unit {R : Type*} [semiring R] [nontrivial R] {f : power_series R} :
  is_unit f → f.order = 0 :=
begin
  rintros ⟨⟨u, v, hu, hv⟩, hf⟩,
  apply and.left,
  rw [← add_eq_zero_iff, ← hf, ← nonpos_iff_eq_zero, ← @power_series.order_one R _ _, ← hu],
  exact power_series.order_mul_ge _ _,
end

variables {K : Type*} [field K]

lemma irreducible_X : irreducible (power_series.X : (power_series K)) :=
prime.irreducible power_series.X_prime


open discrete_valuation_ring power_series
open_locale classical

/-- Given a non-zero power series `f`, this is the power series obtained by dividing out the largest
  power of X that divides `f`-/
def divided_by_X_pow {f : power_series K} (hf : f ≠ 0) : (power_series K) :=
(exists_eq_mul_right_of_dvd (power_series.X_pow_order_dvd (order_finite_iff_ne_zero.mpr hf))).some

lemma self_eq_X_pow_mul_divided_by_X_pow {f : power_series K} (hf : f ≠ 0) :
  X^(f.order.get (order_finite_iff_ne_zero.mpr hf)) * (divided_by_X_pow hf) = f :=
begin
  have dvd := power_series.X_pow_order_dvd (order_finite_iff_ne_zero.mpr hf),
  exact (exists_eq_mul_right_of_dvd dvd).some_spec.symm,
end

@[simp]
lemma divided_by_X_pow_of_X_eq_one : divided_by_X_pow (@X_ne_zero K _ _) = 1 :=
  by simpa only [order_X, X_ne_zero, part_enat.get_one, pow_one, mul_eq_left₀, ne.def, not_false_iff]
    using (self_eq_X_pow_mul_divided_by_X_pow (@X_ne_zero K _ _))

lemma divided_by_X_pow_mul {f g : power_series K} (hf : f ≠ 0) (hg : g ≠ 0) :
  (divided_by_X_pow hf) * (divided_by_X_pow hg) = (divided_by_X_pow (mul_ne_zero hf hg)) :=
begin
  let df := f.order.get (order_finite_iff_ne_zero.mpr hf),
  let dg := g.order.get (order_finite_iff_ne_zero.mpr hg),
  let dfg := (f * g).order.get (order_finite_iff_ne_zero.mpr (mul_ne_zero hf hg)),
  have H_add_d : df + dg = dfg := by simp only [dfg, df, dg, order_mul f g, part_enat.get_add],
  have H := self_eq_X_pow_mul_divided_by_X_pow (mul_ne_zero hf hg),
  have : f * g = X ^ (dfg) * ((divided_by_X_pow hf) * (divided_by_X_pow hg)),
  { calc f * g = X^df * (divided_by_X_pow hf) * (X^dg *
                  (divided_by_X_pow hg)) : by simp only [self_eq_X_pow_mul_divided_by_X_pow]
           ... = X^df * X^dg * (divided_by_X_pow hf) * 
                  (divided_by_X_pow hg) : by ring
           ... = X^(df + dg)*(divided_by_X_pow hf) * (divided_by_X_pow hg) : by {rw [pow_add]}
           ... = X^dfg * (divided_by_X_pow hf) * (divided_by_X_pow hg) : by {rw [H_add_d]}
           ... = X^dfg * ((divided_by_X_pow hf) * (divided_by_X_pow hg)) : by {rw [mul_assoc]}, },
    simp_rw [← dfg, this] at H,
    convert (is_domain.mul_left_cancel_of_ne_zero _ H).symm,
    exact pow_ne_zero dfg X_ne_zero,
end
 

/-- `first_unit_coeff` is the non-zero coefficient whose index is `f.order`, seen as a unit of the
  field.-/
def first_unit_coeff {f : power_series K} (hf : f ≠ 0) : Kˣ := 
begin
  set d := f.order.get (power_series.order_finite_iff_ne_zero.mpr hf) with hd,
  have f_const : power_series.coeff K d f ≠ 0 := by apply power_series.coeff_order,
  haveI : invertible (power_series.constant_coeff K (divided_by_X_pow hf)),
    { apply invertible_of_nonzero,
      convert f_const,
      rw [← power_series.coeff_zero_eq_constant_coeff, ← zero_add d],
      convert (power_series.coeff_X_pow_mul ((exists_eq_mul_right_of_dvd
        (power_series.X_pow_order_dvd (power_series.order_finite_iff_ne_zero.mpr hf))).some) 
          d 0).symm,
      exact (self_eq_X_pow_mul_divided_by_X_pow hf).symm },
  use unit_of_invertible (power_series.constant_coeff K (divided_by_X_pow hf)),
end

/-- `divided_by_X_pow_inv` is the inverse of the element obtained by diving a non-zero power series
by the larges power of `X` dividing it. Useful to create a term of type `units` -/
def divided_by_X_pow_inv {f : power_series K} (hf : f ≠ 0) : power_series K :=
power_series.inv_of_unit ((divided_by_X_pow hf)) (first_unit_coeff hf)

lemma divided_by_X_pow_inv_right_inv {f : power_series K} (hf : f ≠ 0) :
  (divided_by_X_pow hf) * (divided_by_X_pow_inv hf) = 1 :=
mul_inv_of_unit (divided_by_X_pow hf) (first_unit_coeff hf) rfl

lemma divided_by_X_pow_inv_left_inv {f : power_series K} (hf : f ≠ 0) :
   (divided_by_X_pow_inv hf) * (divided_by_X_pow hf) = 1 :=
by {rw mul_comm, exact mul_inv_of_unit (divided_by_X_pow hf) (first_unit_coeff hf) rfl}

/-- `unit_of_divided_by_X_pow` is the unit of power series obtained by dividing a non-zero power
series by the largest power of `X` that divides it. -/
def unit_of_divided_by_X_pow (f : power_series K) : (power_series K)ˣ :=
if hf : f = 0 then 1 else 
{ val := (divided_by_X_pow hf),
  inv := divided_by_X_pow_inv hf,
  val_inv := divided_by_X_pow_inv_right_inv hf,
  inv_val := divided_by_X_pow_inv_left_inv hf }

lemma is_unit_divided_by_X_pow {f : power_series K} (hf : f ≠ 0): is_unit (divided_by_X_pow hf) :=
⟨unit_of_divided_by_X_pow f, by simp only [unit_of_divided_by_X_pow, dif_neg hf, units.coe_mk]⟩

lemma unit_of_divided_by_X_pow_nonzero {f : power_series K} (hf : f ≠ 0) :
  ↑(unit_of_divided_by_X_pow f) = divided_by_X_pow hf :=
by simp only [unit_of_divided_by_X_pow, dif_neg hf, units.coe_mk]

lemma unit_of_divided_by_X_pow_zero : unit_of_divided_by_X_pow (0 : power_series K) = 1 :=
by simp only [unit_of_divided_by_X_pow, dif_pos]

lemma eq_divided_by_X_iff_unit {f : power_series K} (hf : f ≠ 0) :
  f = divided_by_X_pow hf ↔ (is_unit f) :=
⟨λ h, by {rw h, exact is_unit_divided_by_X_pow hf}, λ h,
begin
  have : f.order.get (order_finite_iff_ne_zero.mpr hf) = 0 :=
    by simp only [order_zero_of_unit h, part_enat.get_zero],
  convert (self_eq_X_pow_mul_divided_by_X_pow hf).symm,
  simp only [this, pow_zero, one_mul]
end ⟩

lemma has_unit_mul_pow_irreducible_factorization : 
  has_unit_mul_pow_irreducible_factorization (power_series K) :=
⟨power_series.X, and.intro power_series.irreducible_X 
  begin
    intros f hf,
    use f.order.get (power_series.order_finite_iff_ne_zero.mpr hf),
    use unit_of_divided_by_X_pow f,
    simp only [unit_of_divided_by_X_pow_nonzero hf],
    exact self_eq_X_pow_mul_divided_by_X_pow hf,
  end⟩

instance : unique_factorization_monoid (power_series K) :=
power_series.has_unit_mul_pow_irreducible_factorization.to_unique_factorization_monoid

instance : discrete_valuation_ring (power_series K) :=
of_has_unit_mul_pow_irreducible_factorization
  power_series.has_unit_mul_pow_irreducible_factorization

instance : is_principal_ideal_ring (power_series K) := infer_instance

instance is_noetherian_ring : 
  is_noetherian_ring (power_series K) :=
principal_ideal_ring.is_noetherian_ring

variable (K)
lemma maximal_ideal_eq_span_X : 
  local_ring.maximal_ideal (power_series K) = ideal.span {power_series.X} :=
begin
  have hX : (ideal.span {(power_series.X : power_series K)}).is_maximal,
  { rw ideal.is_maximal_iff,
    split,
    { rw ideal.mem_span_singleton,
      exact prime.not_dvd_one power_series.X_prime, },
    intros I f hI hfX hfI,
    rw [ideal.mem_span_singleton, power_series.X_dvd_iff] at hfX,
    have hfI0 : power_series.C K (f 0) ∈ I,
    { have : power_series.C K (f 0) = f - (f - power_series.C K (f 0)),
      { rw sub_sub_cancel, },
      rw this,
      apply ideal.sub_mem I hfI,
      apply hI,
      rw [ideal.mem_span_singleton, power_series.X_dvd_iff, map_sub, power_series.constant_coeff_C,
        ← power_series.coeff_zero_eq_constant_coeff_apply, power_series.coeff_zero_eq_eval, 
        sub_eq_zero] },
    rw ← ideal.eq_top_iff_one,
    apply ideal.eq_top_of_is_unit_mem I hfI0 (is_unit.map (power_series.C K) (ne.is_unit hfX)) },
  rw local_ring.eq_maximal_ideal hX,
end

lemma not_is_field (R : Type*) [comm_ring R] [nontrivial R] :
  ¬ is_field (power_series R) :=
begin
  nontriviality R,
  rw ring.not_is_field_iff_exists_ideal_bot_lt_and_lt_top,
  use ideal.span {power_series.X},
  split,
  { rw [bot_lt_iff_ne_bot, ne.def, ideal.span_singleton_eq_bot],
    exact power_series.X_ne_zero, },
  { rw [lt_top_iff_ne_top, ne.def, ideal.eq_top_iff_one, ideal.mem_span_singleton,
      power_series.X_dvd_iff, power_series.constant_coeff_one],
    exact one_ne_zero },
end

instance is_dedekind_domain : 
  is_dedekind_domain (power_series K) := 
is_principal_ideal_ring.is_dedekind_domain (power_series K)

instance : normalization_monoid (power_series K) :=
{ norm_unit := λ f, (unit_of_divided_by_X_pow f)⁻¹,
  norm_unit_zero := by simp only [unit_of_divided_by_X_pow_zero, inv_one],
  norm_unit_mul := λ f g hf hg, by { simp only [← mul_inv, inv_inj],
    simp only [unit_of_divided_by_X_pow_nonzero (mul_ne_zero hf hg), 
    unit_of_divided_by_X_pow_nonzero hf, unit_of_divided_by_X_pow_nonzero hg, units.ext_iff,
    coe_unit_of_invertible, units.coe_mul, divided_by_X_pow_mul] },
  norm_unit_coe_units :=
begin
  intro u,
  set u₀ := u.1 with hu,
  have h₀ : is_unit u₀ := ⟨u, hu.symm⟩,
  rw [inv_inj, units.ext_iff, ← u.val_eq_coe, ← hu, unit_of_divided_by_X_pow_nonzero h₀.ne_zero],
  exact ((eq_divided_by_X_iff_unit h₀.ne_zero).mpr h₀).symm,
end }

open local_ring

lemma constant_coeff_surj (R : Type*) [comm_ring R] : function.surjective (constant_coeff R) :=
λ r, ⟨(C R) r, constant_coeff_C r⟩


lemma ker_constant_coeff_eq_max_ideal : ring_hom.ker (constant_coeff K) = maximal_ideal _ :=
ideal.ext (λ _, by rw [ring_hom.mem_ker, power_series.maximal_ideal_eq_span_X K,
    ideal.mem_span_singleton, X_dvd_iff])

/--The ring isomorphism between the residue field of the ring of power series valued in a field `K`
and `K` itself. -/
definition residue_field_of_power_series : residue_field (power_series K) ≃+* K :=
(ideal.quot_equiv_of_eq (ker_constant_coeff_eq_max_ideal K).symm).trans 
    (ring_hom.quotient_ker_equiv_of_surjective (constant_coeff_surj K))

end power_series

variables {K : Type*} [field K]

namespace polynomial

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