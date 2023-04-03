import field_theory.finite.galois_field
import ring_theory.dedekind_domain.adic_valuation
import ring_theory.dedekind_domain.integral_closure

import ring_theory.valuation.tfae

open_locale discrete_valuation

noncomputable theory

lemma power_series.coeff_zero_eq_eval {K : Type*} [semiring K] (f : power_series K) :
  (power_series.coeff K 0) f = f 0 :=
by simp only [power_series.coeff, mv_power_series.coeff, linear_map.coe_proj,
  function.eval_apply, finsupp.single_zero]

variables {K : Type*} [field K]

lemma power_series.irreducible_X : irreducible (power_series.X : (power_series K)) :=
prime.irreducible power_series.X_prime


open discrete_valuation_ring

/- Given a non-zero power series, this is the power series obtained by dividing out the largest
  power of X-/
def divide_X_pow_order {f : power_series K} (hf : f ≠ 0) : (power_series K) :=
(exists_eq_mul_right_of_dvd (power_series.X_pow_order_dvd
  (power_series.order_finite_iff_ne_zero.mpr hf))).some

lemma divide_X_pow_order_mul {f : power_series K} (hf : f ≠ 0) : f =
  (power_series.X)^(f.order.get (power_series.order_finite_iff_ne_zero.mpr hf)) *
    divide_X_pow_order hf :=
begin
  have dvd := power_series.X_pow_order_dvd (power_series.order_finite_iff_ne_zero.mpr hf),
  exact (exists_eq_mul_right_of_dvd dvd).some_spec,
end

/-Given a non-zero power series, the power series obtained in `divide_X_pow_order` is invertible-/
lemma is_invertible_divide_X_pow_order {f : power_series K} (hf : f ≠ 0) :
  invertible (divide_X_pow_order hf) :=
begin
  set d := f.order.get (power_series.order_finite_iff_ne_zero.mpr hf) with hd,
  have f_const : power_series.coeff K d f ≠ 0 := by apply power_series.coeff_order,
  have dvd := power_series.X_pow_order_dvd (power_series.order_finite_iff_ne_zero.mpr hf),
  let const : Kˣ,
  { haveI : invertible (power_series.constant_coeff K (divide_X_pow_order hf)),
    { apply invertible_of_nonzero,
      convert f_const,
      rw [← power_series.coeff_zero_eq_constant_coeff, ← zero_add d],
      convert (power_series.coeff_X_pow_mul ((exists_eq_mul_right_of_dvd
        (power_series.X_pow_order_dvd (power_series.order_finite_iff_ne_zero.mpr hf))).some) 
          d 0).symm,
      apply divide_X_pow_order_mul},
    use unit_of_invertible (power_series.constant_coeff K (divide_X_pow_order hf)) },
  apply invertible.mk (power_series.inv_of_unit ((divide_X_pow_order hf)) const),
  rw mul_comm,
  all_goals {exact power_series.mul_inv_of_unit (divide_X_pow_order hf) const rfl},
end


/-Given a non-zero power series, the unit obtained in `divide_X_pow_order_is_unit`-/
def unit_of_divide_X_pow_order {f : power_series K} (hf : f ≠ 0) : (power_series K)ˣ :=
@unit_of_invertible _ _ (divide_X_pow_order hf) (is_invertible_divide_X_pow_order hf)


lemma power_series.has_unit_mul_pow_irreducible_factorization : 
  has_unit_mul_pow_irreducible_factorization (power_series K) :=
⟨power_series.X, and.intro power_series.irreducible_X 
  begin
    intros f hf,
    use f.order.get (power_series.order_finite_iff_ne_zero.mpr hf),
    use unit_of_divide_X_pow_order hf,
    exact (divide_X_pow_order_mul hf).symm,
  end⟩

instance : unique_factorization_monoid (power_series K) :=
power_series.has_unit_mul_pow_irreducible_factorization.to_unique_factorization_monoid

instance : discrete_valuation_ring (power_series K) :=
of_has_unit_mul_pow_irreducible_factorization
  power_series.has_unit_mul_pow_irreducible_factorization

-- This makes inference faster
instance : is_principal_ideal_ring (power_series K) := infer_instance

instance power_series.is_noetherian_ring (K : Type*) [field K]: 
  is_noetherian_ring (power_series K) :=
principal_ideal_ring.is_noetherian_ring


lemma power_series.maximal_ideal_eq_span_X {K : Type*} [field K] :
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

lemma power_series.not_is_field (R : Type*) [comm_ring R] [nontrivial R] :
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

instance power_series.is_dedekind_domain (K : Type*) [field K] : 
  is_dedekind_domain (power_series K) := 
is_principal_ideal_ring.is_dedekind_domain (power_series K)
