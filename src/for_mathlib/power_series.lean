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


open discrete_valuation_ring power_series
open_locale classical

/- Given a non-zero power series `f`, this is the power series obtained by dividing out the largest
  power of X that divides `f`-/
def fae_order {f : power_series K} (hf : f ≠ 0) : ℕ := 0

def divided_by_X_pow {f : power_series K} (hf : f ≠ 0) : (power_series K) := f
-- (exists_eq_mul_right_of_dvd (power_series.X_pow_order_dvd
--   (order_finite_iff_ne_zero.mpr hf))).some

lemma eq_X_pow_mul_divided_by_X_pow {f : power_series K} (hf : f ≠ 0) : f =
  (power_series.X)^(fae_order hf) *
  -- (power_series.X)^(f.order.get (order_finite_iff_ne_zero.mpr hf)) *
    (divided_by_X_pow hf) :=
begin
  rw [fae_order, pow_zero, one_mul, divided_by_X_pow],

  -- sorry,
  -- have dvd := power_series.X_pow_order_dvd (order_finite_iff_ne_zero.mpr hf),
  -- exact (exists_eq_mul_right_of_dvd dvd).some_spec,
end

lemma divided_by_X_pow_mul {f g : power_series K} (hf : f ≠ 0) (hg : g ≠ 0) :
  (divided_by_X_pow hf) * (divided_by_X_pow hg) = (divided_by_X_pow (mul_ne_zero hf hg)) :=
begin
  have hfg := (mul_ne_zero hf hg),
  -- have hfg₁ := order_finite_iff_ne_zero.mpr hfg,
  -- have hf₁ := (X_pow_order_dvd (order_finite_iff_ne_zero.mpr hf)),
  -- have hg₁ := (X_pow_order_dvd
  -- (power_series.order_finite_iff_ne_zero.mpr hg)),
  have hf₂ := (order_finite_iff_ne_zero.mpr hf),
  have hg₂ := (order_finite_iff_ne_zero.mpr hg),
  have hfg₂ := (order_finite_iff_ne_zero.mpr hfg),
  -- have h_div := mul_dvd_mul hf₁ hg₁,
  -- have h4 := order_mul f g,
  -- have Hd : (f.order + g.order).dom,
  -- {rw ← h4,
  -- use hfg₁},
  -- have h5 := part_enat.get_add Hd,
  -- rw [← pow_add, ← h5] at h_div,
  have h6 := eq_X_pow_mul_divided_by_X_pow hf,
  have h62 : f * g = ((power_series.X ^ (fae_order hf)) * (divided_by_X_pow hf)) * g,
  -- have h62 : f * g = power_series.X ^ (f.order.get hf₂) * (divided_by_X_pow hf) * g,
  rw h6,
  have h7 := eq_X_pow_mul_divided_by_X_pow hg,
  have h8 := eq_X_pow_mul_divided_by_X_pow hfg,
  have final : f * g = power_series.X ^ ((f * g).order.get hfg₂) * (divided_by_X_pow hf)
    * (divided_by_X_pow hg),
  calc f * g = power_series.X ^ (f.order.get hf₂) *
                (divided_by_X_pow hf) * g : by sorry
         ... = power_series.X ^ (f.order.get hf₂) * (divided_by_X_pow hf) * 
                power_series.X ^ (g.order.get hg₂) * (divided_by_X_pow hg) : by sorry
         ... = power_series.X ^ ((f.order.get hf₂) + (g.order.get hg₂)) * (divided_by_X_pow hf) 
                  * (divided_by_X_pow hg) : by sorry
         ... = power_series.X ^ ((f * g).order.get hfg₂) * (divided_by_X_pow hf)
    * (divided_by_X_pow hg) : by sorry,
  have h9 : X ^ ((f * g).order.get hfg₂) * divided_by_X_pow hfg =
    X ^ (f * g).order.get hfg₂ * divided_by_X_pow hf,
  -- rw final,
  -- simp_rw final,

  


  
  
  rw divided_by_X_pow,
  rw divided_by_X_pow,
  rw divided_by_X_pow,
  simp_rw this,
  sorry,
end


/-Given a non-zero power series, the power series obtained in `divided_by_X_pow` is invertible-/
lemma is_invertible_divided_by_X_pow {f : power_series K} (hf : f ≠ 0) :
  invertible (divided_by_X_pow hf) :=
begin
  set d := f.order.get (power_series.order_finite_iff_ne_zero.mpr hf) with hd,
  have f_const : power_series.coeff K d f ≠ 0 := by apply power_series.coeff_order,
  have dvd := power_series.X_pow_order_dvd (power_series.order_finite_iff_ne_zero.mpr hf),
  let const : Kˣ,
  { haveI : invertible (power_series.constant_coeff K (divided_by_X_pow hf)),
    { apply invertible_of_nonzero,
      convert f_const,
      rw [← power_series.coeff_zero_eq_constant_coeff, ← zero_add d],
      convert (power_series.coeff_X_pow_mul ((exists_eq_mul_right_of_dvd
        (power_series.X_pow_order_dvd (power_series.order_finite_iff_ne_zero.mpr hf))).some) 
          d 0).symm,
      apply eq_X_pow_mul_divided_by_X_pow},
    use unit_of_invertible (power_series.constant_coeff K (divided_by_X_pow hf)) },
  apply invertible.mk (power_series.inv_of_unit ((divided_by_X_pow hf)) const),
  rw mul_comm,
  all_goals {exact power_series.mul_inv_of_unit (divided_by_X_pow hf) const rfl},
end


/-Given a non-zero power series, the unit obtained in `divide_X_pow_order_is_unit`-/
-- noncomputable
def unit_of_divided_by_X_pow (f : power_series K) : (power_series K)ˣ :=
if hf : f = 0 then 1 else 
  @unit_of_invertible _ _ (divided_by_X_pow hf) (is_invertible_divided_by_X_pow hf)

@[simp]
lemma unit_of_divide_X_pow_order_nonzero {f : power_series K} (hf : f ≠ 0) :
  unit_of_divided_by_X_pow f = @unit_of_invertible _ _ (divided_by_X_pow hf)
    (is_invertible_divided_by_X_pow hf) := by simp only [unit_of_divided_by_X_pow, dif_neg hf]

@[simp]
lemma unit_of_divide_X_pow_order_zero : unit_of_divided_by_X_pow (0 : power_series K) = 1 :=
by simp only [unit_of_divided_by_X_pow, dif_pos]

lemma power_series.has_unit_mul_pow_irreducible_factorization : 
  has_unit_mul_pow_irreducible_factorization (power_series K) :=
⟨power_series.X, and.intro power_series.irreducible_X 
  begin
    intros f hf,
    use f.order.get (power_series.order_finite_iff_ne_zero.mpr hf),
    use unit_of_divided_by_X_pow f,
    simp only [unit_of_divide_X_pow_order_nonzero hf],
    exact (eq_X_pow_mul_divided_by_X_pow hf).symm,
  end⟩

instance : unique_factorization_monoid (power_series K) :=
power_series.has_unit_mul_pow_irreducible_factorization.to_unique_factorization_monoid

instance : discrete_valuation_ring (power_series K) :=
of_has_unit_mul_pow_irreducible_factorization
  power_series.has_unit_mul_pow_irreducible_factorization

-- This makes inference faster
instance : is_principal_ideal_ring (power_series K) := infer_instance

instance power_series.is_noetherian_ring [field K]: 
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


instance power_series.is_dedekind_domain [field K] : 
  is_dedekind_domain (power_series K) := 
is_principal_ideal_ring.is_dedekind_domain (power_series K)

instance : normalization_monoid (power_series K) :=
{ norm_unit := _,
  norm_unit_zero := _,
  norm_unit_mul := _,
  norm_unit_coe_units := _ }
