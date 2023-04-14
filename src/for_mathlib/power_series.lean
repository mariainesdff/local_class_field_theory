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

lemma order_zero_of_unit {R : Type*} [semiring R] [nontrivial R] {f : power_series R} :
  is_unit f → f.order = 0 :=
begin
  rintros ⟨⟨u, v, hu, hv⟩, hf⟩,
  simp only [units.coe_mk] at hf,--inutile!
  apply and.left,
  rw [← add_eq_zero_iff, ← hf, ← nonpos_iff_eq_zero, ← @power_series.order_one R _ _, ← hu],
  exact power_series.order_mul_ge _ _,
end

variables {K : Type*} [field K]

lemma power_series.irreducible_X : irreducible (power_series.X : (power_series K)) :=
prime.irreducible power_series.X_prime


open discrete_valuation_ring power_series
open_locale classical

/- Given a non-zero power series `f`, this is the power series obtained by dividing out the largest
  power of X that divides `f`-/
def divided_by_X_pow {f : power_series K} (hf : f ≠ 0) : (power_series K) :=
(exists_eq_mul_right_of_dvd (power_series.X_pow_order_dvd (order_finite_iff_ne_zero.mpr hf))).some

lemma self_eq_X_pow_mul_divided_by_X_pow {f : power_series K} (hf : f ≠ 0) :
  X^(f.order.get (order_finite_iff_ne_zero.mpr hf)) * (divided_by_X_pow hf) = f :=
begin
  have dvd := power_series.X_pow_order_dvd (order_finite_iff_ne_zero.mpr hf),
  exact (exists_eq_mul_right_of_dvd dvd).some_spec.symm,
end

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
                  (divided_by_X_pow hg)) : by {simp only [self_eq_X_pow_mul_divided_by_X_pow]}
           ... = X^df * X^dg * (divided_by_X_pow hf) * 
                  (divided_by_X_pow hg) : by ring
           ... = X^(df + dg)*(divided_by_X_pow hf) * (divided_by_X_pow hg) : by {rw [pow_add]}
           ... = X^dfg * (divided_by_X_pow hf) * (divided_by_X_pow hg) : by {rw [H_add_d]}
           ... = X^dfg * ((divided_by_X_pow hf) * (divided_by_X_pow hg)) : by {rw [mul_assoc]}, },
    simp_rw [← dfg, this] at H,
    convert (is_domain.mul_left_cancel_of_ne_zero _ H).symm,
    exact pow_ne_zero dfg X_ne_zero,
end

def divided_by_X_pow_inv {f : power_series K} (hf : f ≠ 0) : power_series K :=
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
      exact (self_eq_X_pow_mul_divided_by_X_pow hf).symm },
      use unit_of_invertible (power_series.constant_coeff K (divided_by_X_pow hf)) },
  -- use ⟨divided_by_X_pow hf, 
  use power_series.inv_of_unit ((divided_by_X_pow hf)) const,
    -- mul_inv_of_unit (divided_by_X_pow hf) const rfl, by {rw mul_comm, exact mul_inv_of_unit
    -- (divided_by_X_pow hf) const rfl}⟩,
end

lemma divided_by_X_pow_inv_right_inv {f : power_series K} (hf : f ≠ 0) :
  (divided_by_X_pow hf) * (divided_by_X_pow_inv hf) = 1 := sorry

lemma divided_by_X_pow_inv_left_inv {f : power_series K} (hf : f ≠ 0) :
   (divided_by_X_pow_inv hf) * (divided_by_X_pow hf) = 1 := sorry

def unit_of_divided_by_X_pow' (f : power_series K) : (power_series K)ˣ :=
if hf : f = 0 then 1 else 
{ val := (divided_by_X_pow hf),
  inv := divided_by_X_pow_inv hf,
  val_inv := divided_by_X_pow_inv_right_inv hf,
  inv_val := divided_by_X_pow_inv_left_inv hf }
-- begin
--   set d := f.order.get (power_series.order_finite_iff_ne_zero.mpr hf) with hd,
--   have f_const : power_series.coeff K d f ≠ 0 := by apply power_series.coeff_order,
--   have dvd := power_series.X_pow_order_dvd (power_series.order_finite_iff_ne_zero.mpr hf),
--   let const : Kˣ,
--   { haveI : invertible (power_series.constant_coeff K (divided_by_X_pow hf)),
--     { apply invertible_of_nonzero,
--       convert f_const,
--       rw [← power_series.coeff_zero_eq_constant_coeff, ← zero_add d],
--       convert (power_series.coeff_X_pow_mul ((exists_eq_mul_right_of_dvd
--         (power_series.X_pow_order_dvd (power_series.order_finite_iff_ne_zero.mpr hf))).some) 
--           d 0).symm,
--       exact (self_eq_X_pow_mul_divided_by_X_pow hf).symm },
--       use unit_of_invertible (power_series.constant_coeff K (divided_by_X_pow hf)) },
--   use ⟨divided_by_X_pow hf, power_series.inv_of_unit ((divided_by_X_pow hf)) const,
--     mul_inv_of_unit (divided_by_X_pow hf) const rfl, by {rw mul_comm, exact mul_inv_of_unit
--     (divided_by_X_pow hf) const rfl}⟩,
-- end

/-Given a non-zero power series, the power series obtained in `divided_by_X_pow` is a unit-/
-- lemma is_unit_divided_by_X_pow {f : power_series K} (hf : f ≠ 0) :
--   is_unit (divided_by_X_pow hf) :=
-- begin
--   set d := f.order.get (power_series.order_finite_iff_ne_zero.mpr hf) with hd,
--   have f_const : power_series.coeff K d f ≠ 0 := by apply power_series.coeff_order,
--   have dvd := power_series.X_pow_order_dvd (power_series.order_finite_iff_ne_zero.mpr hf),
--   let const : Kˣ,
--   { haveI : invertible (power_series.constant_coeff K (divided_by_X_pow hf)),
--     { apply invertible_of_nonzero,
--       convert f_const,
--       rw [← power_series.coeff_zero_eq_constant_coeff, ← zero_add d],
--       convert (power_series.coeff_X_pow_mul ((exists_eq_mul_right_of_dvd
--         (power_series.X_pow_order_dvd (power_series.order_finite_iff_ne_zero.mpr hf))).some) 
--           d 0).symm,
--       exact (self_eq_X_pow_mul_divided_by_X_pow hf).symm },
--       use unit_of_invertible (power_series.constant_coeff K (divided_by_X_pow hf)) },
--   exact ⟨⟨divided_by_X_pow hf, power_series.inv_of_unit ((divided_by_X_pow hf)) const,
--     mul_inv_of_unit (divided_by_X_pow hf) const rfl, by {rw mul_comm, exact mul_inv_of_unit
--     (divided_by_X_pow hf) const rfl}⟩, rfl⟩,
-- end

-- /-Given a non-zero power series, the power series obtained in `divided_by_X_pow` is invertible-/
-- lemma is_invertible_divided_by_X_pow {f : power_series K} (hf : f ≠ 0) :
--   invertible (divided_by_X_pow hf) :=
-- begin
--   set d := f.order.get (power_series.order_finite_iff_ne_zero.mpr hf) with hd,
--   have f_const : power_series.coeff K d f ≠ 0 := by apply power_series.coeff_order,
--   have dvd := power_series.X_pow_order_dvd (power_series.order_finite_iff_ne_zero.mpr hf),
--   let const : Kˣ,
--   { haveI : invertible (power_series.constant_coeff K (divided_by_X_pow hf)),
--     { apply invertible_of_nonzero,
--       convert f_const,
--       rw [← power_series.coeff_zero_eq_constant_coeff, ← zero_add d],
--       convert (power_series.coeff_X_pow_mul ((exists_eq_mul_right_of_dvd
--         (power_series.X_pow_order_dvd (power_series.order_finite_iff_ne_zero.mpr hf))).some) 
--           d 0).symm,
--       exact (self_eq_X_pow_mul_divided_by_X_pow hf).symm },
--     use unit_of_invertible (power_series.constant_coeff K (divided_by_X_pow hf)) },
--   apply invertible.mk (power_series.inv_of_unit ((divided_by_X_pow hf)) const),
--   rw mul_comm,
--   all_goals {exact power_series.mul_inv_of_unit (divided_by_X_pow hf) const rfl},
-- end


/-Given a non-zero power series, the unit obtained in `divide_X_pow_order_is_unit`-/
-- noncomputable
-- def unit_of_divided_by_X_pow (f : power_series K) : (power_series K)ˣ :=
-- if hf : f = 0 then 1 else 
-- -- begin
--   -- @unit_of_invertible _ _ (divided_by_X_pow hf) (is_invertible_divided_by_X_pow hf)
--   (is_unit_divided_by_X_pow hf).some
-- end

-- lemma unit_of_divided_by_X_pow_nonzero {f : power_series K} (hf : f ≠ 0) :
--   unit_of_divided_by_X_pow f = f 
--   unit_of_divided_by_X_pow f = @unit_of_invertible _ _ (divided_by_X_pow hf)
--     (is_invertible_divided_by_X_pow hf) := by simp only [unit_of_divided_by_X_pow, dif_neg hf]

lemma is_unit_divided_by_X_pow {f : power_series K} (hf : f ≠ 0): is_unit (divided_by_X_pow hf) :=
begin
  use unit_of_divided_by_X_pow' f,
  simp [unit_of_divided_by_X_pow'],
  rw [dif_neg hf],
  simp only [units.coe_mk],
end

lemma unit_of_divided_by_X_pow_zero : unit_of_divided_by_X_pow' (0 : power_series K) = 1 :=
by simp only [unit_of_divided_by_X_pow', dif_pos]

lemma eq_divided_by_X_iff_unit {f : power_series K} (hf : f ≠ 0) :
  f = divided_by_X_pow hf ↔ (is_unit f) :=
begin
  split,
  { intro hf₁,
    rw hf₁,
    exact is_unit_divided_by_X_pow hf,
    -- set u := unit_of_divided_by_X_pow' f with hu,
    -- use u,
    -- simp [hu, coe_unit_of_invertible],
    -- rw hf₁,
    -- simp,
  --   simp [hu, unit_of_divided_by_X_pow_nonzero hf, coe_unit_of_invertible],
    -- convert hf₁.symm, },
  },
  -- { intro hf₁,
  --   have : f.order.get (order_finite_iff_ne_zero.mpr hf) = 0 :=
  --     by simp only [order_zero_of_unit hf₁, part_enat.get_zero],
  --   convert (self_eq_X_pow_mul_divided_by_X_pow hf).symm,
  --   simp only [this, pow_zero, one_mul] }

end

lemma power_series.has_unit_mul_pow_irreducible_factorization : 
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
{ norm_unit :=
begin
  intro f,
  use (unit_of_divided_by_X_pow f)⁻¹,
end,
  norm_unit_zero :=
begin
  simp [unit_of_divided_by_X_pow_zero],
end,
  norm_unit_mul :=
begin
  intros f g hf hg,
  rw [← mul_inv],
  congr,
  simp only [unit_of_divided_by_X_pow_nonzero (mul_ne_zero hf hg),
    unit_of_divided_by_X_pow_nonzero hf, unit_of_divided_by_X_pow_nonzero hg, units.ext_iff,
    coe_unit_of_invertible, units.coe_mul, divided_by_X_pow_mul],
end,
  norm_unit_coe_units :=
begin
  rintros ⟨u, v, h1, h2⟩,
  -- let u := v.1,
  have hu : is_unit u := sorry,--⟨v, rfl⟩,
  have h : v = u⁻¹, sorry,
  -- have h1 : u ≠ 0,
  -- exact h2.ne_zero,
  simp only [inv_inj],
  have uff' := (eq_divided_by_X_iff_unit hu.ne_zero).mpr hu,
  have uff : u⁻¹ = (divided_by_X_pow hu.ne_zero)⁻¹,
  congr,
  exact uff',
  -- replace this := 
  have H := unit_of_divided_by_X_pow_nonzero hu.ne_zero,
  -- simp [H, this],/
  -- convert_to unit_of_divided_by_X_pow u = v,
  convert H,
  rw h,
  -- rw inv_eq_one_divp,
  convert uff,
  refine (cast_inj _).mp _,
  -- simp [this],
  -- rw inv_eq
  -- simp,
  -- convert this,
  -- rw coe_unit_of_invertible,
  -- simp [this],
  -- change
  -- convert this using 0,
  -- simp_rw this at H,
  -- simp [unit_of_divided_by_X_pow_nonzero h1] at this,
  -- rw units.coe

  -- simp [this],
  -- have v : (power_series K)
  -- have hu : is_unit u,
  -- rintros ⟨u, v, h1, h2⟩,
  -- have hu₁ : u ≠ 0, sorry,
  -- have hu₂ : is_unit u, sorry,
  -- have := (eq_divided_by_X_iff_unit hu₁).mpr hu₂,
  -- simp [unit_of_divided_by_X_pow_nonzero hu₁],
  -- have H : u⁻¹ = v, sorry,
  -- have falso : unit_of_invertible (divided_by_X_pow hu₁) = (divided_by_X_pow hu₁),sorry,
  -- rw this at H,
  -- convert [H],
  -- sorry,
  -- simp_rw [← this],
  -- simp [← coe_unit_of_invertible],
  -- ext,
  -- convert this.symm,
  -- simp [this],
end }
