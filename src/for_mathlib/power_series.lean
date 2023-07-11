import field_theory.finite.galois_field
import ring_theory.dedekind_domain.adic_valuation
import ring_theory.dedekind_domain.integral_closure
import ring_theory.power_series.basic
import ring_theory.valuation.valuation_subring

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
 

/- `first_unit_coeff` is the non-zero coefficient whose index is `f.order`, seen as a unit of the
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

def divided_by_X_pow_inv {f : power_series K} (hf : f ≠ 0) : power_series K :=
begin
  use power_series.inv_of_unit ((divided_by_X_pow hf)) (first_unit_coeff hf),

  -- set d := f.order.get (power_series.order_finite_iff_ne_zero.mpr hf) with hd,
  -- have f_const : power_series.coeff K d f ≠ 0 := by apply power_series.coeff_order,
  -- have dvd := power_series.X_pow_order_dvd (power_series.order_finite_iff_ne_zero.mpr hf),
  -- let const : Kˣ,
  -- { haveI : invertible (power_series.constant_coeff K (divided_by_X_pow hf)),
  --   { apply invertible_of_nonzero,
  --     convert f_const,
  --     rw [← power_series.coeff_zero_eq_constant_coeff, ← zero_add d],
  --     convert (power_series.coeff_X_pow_mul ((exists_eq_mul_right_of_dvd
  --       (power_series.X_pow_order_dvd (power_series.order_finite_iff_ne_zero.mpr hf))).some) 
  --         d 0).symm,
  --     exact (self_eq_X_pow_mul_divided_by_X_pow hf).symm },
  --     use unit_of_invertible (power_series.constant_coeff K (divided_by_X_pow hf)) },
  
  -- use power_series.inv_of_unit ((divided_by_X_pow hf)) const,

  -- use ⟨divided_by_X_pow hf, 
    -- mul_inv_of_unit (divided_by_X_pow hf) const rfl, by {rw mul_comm, exact mul_inv_of_unit
    -- (divided_by_X_pow hf) const rfl}⟩,
end

lemma divided_by_X_pow_inv_right_inv {f : power_series K} (hf : f ≠ 0) :
  (divided_by_X_pow hf) * (divided_by_X_pow_inv hf) = 1 :=
mul_inv_of_unit (divided_by_X_pow hf) (first_unit_coeff hf) rfl

lemma divided_by_X_pow_inv_left_inv {f : power_series K} (hf : f ≠ 0) :
   (divided_by_X_pow_inv hf) * (divided_by_X_pow hf) = 1 :=
by {rw mul_comm, exact mul_inv_of_unit (divided_by_X_pow hf) (first_unit_coeff hf) rfl}

def unit_of_divided_by_X_pow (f : power_series K) : (power_series K)ˣ :=
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