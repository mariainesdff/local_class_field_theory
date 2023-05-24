/-
Copyright (c) 2022 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import order.filter.basic
import algebra.order.hom.monoid
-- import algebra.hom.group
import for_mathlib.num_denom_away
import for_mathlib.polynomial
import for_mathlib.power_series
import ring_theory.dedekind_domain.adic_valuation
import ring_theory.laurent_series
import ring_theory.power_series.well_known

import algebra_comp

open polynomial is_dedekind_domain.height_one_spectrum topological_space ratfunc
  sequentially_complete filter
open_locale big_operators discrete_valuation uniformity filter topology

variables (K : Type*) [field K]

noncomputable theory
def completion_of_ratfunc := adic_completion (ratfunc K) (ideal_X K)


instance : field (completion_of_ratfunc K) := adic_completion.field (ratfunc K) (ideal_X K)

instance : algebra K (polynomial K) := infer_instance

instance already : valued (completion_of_ratfunc K) ℤₘ₀ :=
  @valued.valued_completion _ _ _ _ (ideal_X K).adic_valued

instance : uniform_space (completion_of_ratfunc K) := infer_instance

variable (F : completion_of_ratfunc K)

def entourage (d : ℤ) : set (ratfunc K × ratfunc K) :=
  {P | (ideal_X K).valuation (P.1 - P.2) < ↑(multiplicative.of_add (- d))}

lemma fae_for_pol (f  : polynomial K) (d : ℕ) (hf : (ideal_X K).int_valuation f ≤ 
  ↑(multiplicative.of_add (- (d+(1 : ℕ)) : ℤ))) : f.coeff d = 0 :=
begin 
  erw [int_valuation_le_pow_iff_dvd _ _ (d+1)] at hf,
  simp only [ideal_X_span, ideal.dvd_span_singleton, ideal.span_singleton_pow,
    ideal.mem_span_singleton'] at hf,
  cases hf with a ha,
  simp only [← ha, coeff_mul_X_pow', add_le_iff_nonpos_right, le_zero_iff, nat.one_ne_zero,
    if_false],
end

open laurent_series hahn_series

lemma val_X_fae : ((X : ratfunc K): laurent_series K).order = 1 :=
by simp only [ratfunc.coe_X, hahn_series.order_single, ne.def, one_ne_zero, not_false_iff]

lemma fae_X_pow (n : ℕ) : (hahn_series.single (n : ℤ) 1) =
  ((X :ratfunc K) : laurent_series K) ^ n :=
begin
induction n with n h_ind ,
    { simp only [nat.nat_zero_eq_zero, int.of_nat_eq_coe, zmod.nat_cast_self, zpow_zero],
     refl, },
    { rw ← int.coe_nat_add_one_out,
      rw [← one_mul (1 : K)],
      rw ← hahn_series.single_mul_single,
      rw h_ind,
      rw ratfunc.coe_X,
      rw pow_succ' },
end

lemma fae_single_inv (d : ℤ) (α : K) (hα : α ≠ 0) : (hahn_series.single (d : ℤ) (α : K))⁻¹ 
  = hahn_series.single (-d) (α⁻¹ : K) :=
by {rw [inv_eq_of_mul_eq_one_left], simpa only [hahn_series.single_mul_single, 
  add_left_neg, inv_mul_cancel hα]}


lemma fae_X_zpow (n : ℤ) : (hahn_series.single (n : ℤ) 1) =
  ((X :ratfunc K) : laurent_series K) ^ n :=
begin
  induction n with n_pos n_neg,
  apply fae_X_pow,
  rw ratfunc.coe_X,
  have := fae_single_inv K ((n_neg + 1) : ℤ) 1 one_ne_zero,
  rw int.neg_succ_of_nat_coe,
  rw int.coe_nat_add,
  rw nat.cast_one,
  nth_rewrite 0 [← inv_one],
  rw ← this,
  rw zpow_neg,
  rw ← nat.cast_one,
  rw ← int.coe_nat_add,
  rw fae_X_pow,
  rw ratfunc.coe_X,
  rw [algebra_map.coe_one, inv_inj],
  rw zpow_coe_nat,
end


namespace hahn_series
open set
variables {Γ Γ' R : Type*}  


lemma eq_order_of_emb_domain [has_zero R] [linear_order Γ] [linear_order Γ'] [has_zero Γ]
    [has_zero Γ'] (φ : hahn_series Γ R) {ι : Γ ↪o Γ'}  (hι : ι 0 = 0) : 
    (emb_domain ι φ).order = ι φ.order :=
begin
  by_cases h : φ = 0,
  { simp [h, hι] },
  have : emb_domain ι φ ≠ 0,
  { intro h0,
    rw [← @emb_domain_zero Γ _ _ _ _ _ ι] at h0,
    exact h (emb_domain_injective h0) },
  rw [order_of_ne h, order_of_ne this],
  refine le_antisymm (is_wf.min_le _ _ _) ((is_wf.le_min_iff _ _).2 (λ b hb, _)),
  { simp only [mem_support, emb_domain_coeff, ne.def],
    intro h0,
    rw [← order_of_ne h] at h0,
    exact coeff_order_ne_zero h h0 },
  { simp only [mem_support, ne.def] at hb,
    replace hb : b ∈ ι '' φ.support,
    { by_contra' habs,
      exact hb (emb_domain_notin_image_support habs) },
    obtain ⟨c, hcmem, hbc⟩ := hb,
    rw [← hbc, ι.le_iff_le],
    exact is_wf.min_le _ _ hcmem },
end

-- **This looks
-- lemma of_power_series_tower (φ : power_series R) [strict_ordered_semiring Γ]
--   [strict_ordered_semiring Γ'] {ι : Γ →+ Γ'} (hinj : function.injective ι) 
--   (hι : ∀ g g' : Γ, ι g ≤ ι g' ↔ g ≤ g') [semiring R] : 
--   (emb_domain ⟨⟨ι, hinj⟩, hι⟩ (of_power_series Γ R φ )) = (of_power_series Γ' R φ) :=
-- begin
--   -- simp,
--   ext g,
--   have := @emb_domain_coeff Γ R _ _ Γ' _ ⟨⟨ι, hinj⟩, hι⟩ (of_power_series Γ R φ),
-- end

lemma order_eq_of_power_series {R : Type*} [semiring R] {φ : power_series R} (hφ : φ ≠ 0) :
  power_series.order φ = (hahn_series.of_power_series ℕ R φ).order :=
begin
  -- by_cases hφ : φ = 0,
  -- { rw hφ,
  --   rw power_series.order_zero,
  --   rw map_zero,
  --   rw hahn_series.order_zero,
  --   simp,
  --   sorry--and it is false
  -- },
  obtain ⟨_, ⟨H, hm⟩⟩ := part.dom_iff_mem.mp ((power_series.order_finite_iff_ne_zero).mpr hφ),
    rw [← @part_enat.coe_get _ H],
    apply congr_arg,
    apply le_antisymm _ (hahn_series.order_le_of_coeff_ne_zero _),
    { rw [← part_enat.coe_le_coe, part_enat.coe_get],
      apply power_series.order_le,
      erw [← @hahn_series.of_power_series_apply_coeff ℕ _ _ _ _ _],
      apply hahn_series.coeff_order_ne_zero,
      exact (map_ne_zero_iff (hahn_series.of_power_series ℕ R)
        (hahn_series.of_power_series_injective)).mpr hφ,
    },
    { erw [hahn_series.of_power_series_apply_coeff φ],
      apply power_series.coeff_order, },
end

lemma to_power_series_of_power_series {R : Type*} [semiring R] {φ : hahn_series ℕ R} :
  of_power_series ℕ R (to_power_series φ) = φ :=
begin
  ext,
  convert of_power_series_apply_coeff (to_power_series φ) _,
  simp only [finsupp.single_eq_same],
end

lemma order_eq_to_power_series {R : Type*} [comm_ring R] {φ : hahn_series ℕ R} (hφ : φ ≠ 0) :
  power_series.order (to_power_series φ) = φ.order :=
by rw [order_eq_of_power_series ((map_ne_zero_iff _ (@to_power_series R _).injective).mpr hφ), to_power_series_of_power_series]

lemma nat_order_eq_of_power_series {R : Type*} [semiring R] {φ : power_series R} (hφ : φ ≠ 0) :
  (φ.order).get (power_series.order_finite_iff_ne_zero.mpr hφ) =
    (hahn_series.of_power_series ℕ R φ).order :=
by simp only [order_eq_of_power_series hφ, part_enat.get_coe']


-- lemma emb_domain_comp {R Γ : Type*} [strict_ordered_semiring Γ] [comm_semiring R] (ι : ℕ ↪o Γ)
--   (φ : power_series R) : emb_domain ι (of_power_series ℕ R φ) = of_power_series Γ R φ := sorry

-- `[FAE]` The proof is **disgusting**, need to isolate (at least) `emb_domain_comp`
lemma order_eq_of_power_series_Z {R : Type*} [comm_semiring R] {φ : power_series R} (hφ : φ ≠ 0) :
  ((φ.order).get (power_series.order_finite_iff_ne_zero.mpr hφ) : ℤ) =
    (hahn_series.of_power_series ℤ R φ).order :=
begin
  let ι : ℕ ↪o ℤ := ⟨⟨(nat.cast_add_monoid_hom ℤ).1, nat.strict_mono_cast.injective⟩, λ _ _, nat.cast_le⟩,
  have := @hahn_series.eq_order_of_emb_domain ℕ ℤ R _ _ _ _ _ (of_power_series ℕ R φ) ι nat.cast_zero,
  have emb_domain_comp' : emb_domain ι (of_power_series ℕ R φ) = of_power_series ℤ R φ,
  { ext n,
    induction n with n m,
    { have uno := @emb_domain_coeff ℕ R _ _ ℤ _ ι (of_power_series ℕ R φ) n,
      erw uno,
      have tre := @of_power_series_apply_coeff ℕ R _ _ φ n,
      simp only [nat.cast_id] at tre,
      rw tre,
      have quattro := @of_power_series_apply_coeff ℤ R _ _ φ n,
      exact quattro.symm},
    { have : (emb_domain ι ((of_power_series ℕ R) φ)).coeff -[1+ m] = 0,
      { apply emb_domain_notin_range,
        simp only [add_monoid_hom.to_fun_eq_coe, nat.coe_cast_add_monoid_hom, rel_embedding.coe_fn_mk, function.embedding.coe_fn_mk,
          mem_range, not_exists],
        intros x H,
        have hx : (0 : ℤ) ≤ x := x.cast_nonneg,
        rw H at hx,
        exact (le_not_le_of_lt (int.neg_succ_of_nat_lt_zero m)).2 hx},
      rw this,
      have h_dif := (@of_power_series_alg_apply_coeff ℤ R _ R _ _ _ φ -[1+m]).symm,
      rwa dif_neg at h_dif,
      simp only [not_exists, not_and],
      rintros x - H,
      have hx : (0 : ℤ) ≤ x := x.cast_nonneg,
      rw H at hx,
      exact (le_not_le_of_lt (int.neg_succ_of_nat_lt_zero m)).2 hx}, },
  rw emb_domain_comp' at this,--use `emb_domain_comp` instead, once it is proved
  rw nat_order_eq_of_power_series,
  symmetry,
  exact this,
end
end hahn_series

-- FAE for `mathlib`?
lemma fae_int_valuation_apply (f : polynomial K) : 
  ((ideal_X K).int_valuation f) = ((ideal_X K).int_valuation_def f) := refl _

-- `FAE` The two lemmas that follow are not `refl` because the iso `to_power_series` is an iso with
-- Hahn series indexed on `ℕ` while `of_power_series` embeds the power series in any ring of Hahn
-- series indexed on a linearly ordered monoid (or blablabla).

lemma of_power_series_to_power_series {R : Type*} [semiring R] {φ : power_series R} :
  to_power_series (of_power_series ℕ R φ) = φ :=
begin
  ext,
  convert @coeff_to_power_series _ _ (of_power_series ℕ R φ) _,
  exact (of_power_series_apply_coeff φ n).symm,
end

-- ***TO DO*** understand what to do with `φ = 0`

lemma X_pow_dvd_pol_iff_dvd_power_series (A : Type*) [comm_ring A] (P : polynomial A) (n : ℕ) :
  (polynomial.X)^n ∣ P ↔ (power_series.X)^n ∣ (P : power_series A) := by
 simp only [power_series.X_pow_dvd_iff, polynomial.X_pow_dvd_iff, coeff_coe]


/-
`FAE`: The strategy for the lemma below should now be to use that
* the order of the hahn_series 
* orders of power_series and of hahn_series ℕ _ are the same by some lemma above
* the order of a power_series is the minimum of the non-zero-coefficients
* this is equivalent to the power series being divisible exactly by X^{ord} by
`power_series.X_pow_dvd_iff`
* this is equivalent to the polynomial being divisible exactly by by X^{ord} by
`X_pow_dvd_pol_iff_dvd_power_series` (that need not be a lemma? or yes?)
* this coincides with the definition of the valuation.
-/

local attribute [instance] classical.prop_decidable

open multiplicity

lemma fae_pol_ps_order_mul {f : polynomial K} : 
  (↑f : power_series K).order = multiplicity polynomial.X f :=
begin
  by_cases hf_pol : f = 0,
  { simp only [hf_pol, polynomial.coe_zero, power_series.order_zero, multiplicity.zero] },
  { rw power_series.order_eq_multiplicity_X,
    have hf_ps : finite (power_series.X : power_series K) ↑f,
    { simpa only [X_pow_dvd_pol_iff_dvd_power_series, multiplicity.finite_def, map_zero, sub_zero]
        using multiplicity_X_sub_C_finite 0 hf_pol },
    set d_ps := (multiplicity power_series.X ↑f).get hf_ps with hd_ps,
    replace hf_pol: finite polynomial.X f,
    { simpa only [multiplicity.finite_def, map_zero, sub_zero]
        using multiplicity_X_sub_C_finite 0 hf_pol },
    set d_pol := (multiplicity polynomial.X f).get hf_pol with hd_pol,
    obtain ⟨P, hfP, -⟩ := exists_eq_pow_mul_and_not_dvd hf_pol,
    rw ← hd_pol at hfP,
    obtain ⟨φ, hfφ, -⟩ := exists_eq_pow_mul_and_not_dvd hf_ps,
    rw ← hd_ps at hfφ,
    apply le_antisymm,
    { have Hpol := @pow_dvd_iff_le_multiplicity (polynomial K) _ _ X f d_ps,
      rw [X_pow_dvd_pol_iff_dvd_power_series] at Hpol,
      replace Hpol := Hpol.mp (dvd_of_mul_right_eq _ hfφ.symm),
      rwa [hd_ps, part_enat.coe_get] at Hpol },
    { have Hps := @pow_dvd_iff_le_multiplicity (power_series K) _ _ power_series.X f d_pol,
      rw [← X_pow_dvd_pol_iff_dvd_power_series] at Hps,
      replace Hps := Hps.mp (dvd_of_mul_right_eq _ hfP.symm),
      rwa [hd_pol, part_enat.coe_get] at Hps }}
end

variable {K}
lemma polynomial.coe_ne_zero {f : polynomial K} : f ≠ 0 → (↑f : (power_series K)) ≠ 0 :=
by simp only [ne.def, coe_eq_zero_iff, imp_self]
variable (K)

--mathlib
variable {K}
lemma finite_multiplicity_of_ne_zero {f : polynomial K} (hf : f ≠ 0) : 
  multiplicity.finite polynomial.X f :=
@multiplicity.finite_prime_left (polynomial K) _ _ _ _ prime_X hf


variable (K)
lemma fae_pol_ps_nat_order_mul {f : polynomial K} (hf : f ≠ 0) :
  ((↑f : power_series K).order).get (power_series.order_finite_iff_ne_zero.mpr
    (polynomial.coe_ne_zero hf)) =
    (multiplicity polynomial.X f).get (finite_multiplicity_of_ne_zero hf) :=
by simpa only [fae_pol_ps_order_mul]


-- section nat_order
-- namespace power_series

variable {K}
-- def nat_order {φ : power_series K} (h : φ ≠ 0) : ℕ := 
--   nat.find (exists_coeff_ne_zero_iff_ne_zero.mpr h)

-- lemma nat_order_eq_order {φ : power_series K} (h : φ ≠ 0) : ↑(nat_order h) = φ.order :=
-- begin
--   simp only [order, ne.def],
--   rw [dif_neg h],
--   simp only [part_enat.coe_inj],
--   sorry,
--   -- apply eq.symm,
--   -- simp,
--   -- refl,
-- end

-- end power_series
-- end nat_order


variable (K)

open unique_factorization_monoid
lemma count_normalized_factors_eq_count_normalized_factors_span {R : Type*} [comm_ring R]
  [is_domain R] [is_principal_ideal_ring R] [normalization_monoid R] [unique_factorization_monoid R] 
    {r X : R} (hr : r ≠ 0) (hX₀ : X ≠ 0) (hX₁ : norm_unit X = 1 )(hX : prime X) : 
  multiset.count X (normalized_factors r) =
    multiset.count (ideal.span {X} : ideal R ) (normalized_factors (ideal.span {r})) :=
begin
  replace hX₁ : X = normalize X, 
  { simp only [normalize_apply, hX₁, units.coe_one, mul_one] },
  have : (ideal.span {normalize X} : ideal  R) = normalize (ideal.span {X}),
  { simp only [normalize_apply, normalize_eq],
    apply ideal.span_singleton_mul_right_unit (units.is_unit _) },
  rw [← part_enat.coe_inj, hX₁, ← multiplicity_eq_count_normalized_factors hX.irreducible hr, this, 
    ← multiplicity_eq_multiplicity_span, ← multiplicity_eq_count_normalized_factors],
  refine prime.irreducible (ideal.prime_of_is_prime _ _),
  {rwa [ne.def, ideal.span_singleton_eq_bot] },
  {rwa ideal.span_singleton_prime hX₀ },
  {rwa [ne.def, ideal.zero_eq_bot, ideal.span_singleton_eq_bot] },
end

--GOLF IT!
lemma count_normalized_factors_eq_associates_count {I J : ideal (polynomial K)} (hI : I ≠ 0)
  (hJ : J.is_prime ) (hJ₀ : J ≠ ⊥) :
  multiset.count J (normalized_factors I) = (associates.mk J).count (associates.mk I).factors :=
begin
  replace hI : associates.mk I ≠ 0,
  { apply associates.mk_ne_zero.mpr hI },
  have hJ' : irreducible (associates.mk J),
  { rw associates.irreducible_mk,
    apply prime.irreducible,
    apply ideal.prime_of_is_prime hJ₀ hJ },
  apply ideal.count_normalized_factors_eq,
  rw [← ideal.dvd_iff_le, ← associates.mk_dvd_mk, associates.mk_pow],
  rw associates.dvd_eq_le,
  rw associates.prime_pow_dvd_iff_le hI hJ',
  { rw ← ideal.dvd_iff_le,
    rw ← associates.mk_dvd_mk,
    rw associates.mk_pow,
    rw associates.dvd_eq_le,
    rw associates.prime_pow_dvd_iff_le hI hJ',
    linarith,
  },
end


-- lemma multiplicity_X_eq_int_valuation {f : polynomial K} (hf : f ≠ 0 ) :
-- -- ↑(multiplicative.of_add 
-- --   (-((↑f : power_series K).order).get (power_series.order_finite_iff_ne_zero.mpr
-- --     (polynomial.coe_ne_zero hf)) : ℤ)) 
--    (multiplicity polynomial.X f).get (multiplicity_finite_iff_ne_zero.mpr hf)
--     = ((ideal_X K).int_valuation f) :=

lemma order_as_power_series_eq_int_valuation {f : polynomial K} (hf : f ≠ 0) :
  ↑(multiplicative.of_add 
  (-((↑f : power_series K).order).get (power_series.order_finite_iff_ne_zero.mpr
    (polynomial.coe_ne_zero hf)) : ℤ)) = ((ideal_X K).int_valuation f) :=
begin
  rw [fae_pol_ps_nat_order_mul, fae_int_valuation_apply, int_valuation_def_if_neg _ hf],
  simp only [of_add_neg, ideal_X_span, inv_inj, with_zero.coe_inj, embedding_like.apply_eq_iff_eq,
    nat.cast_inj],
  simp_rw [@multiplicity_eq_count_normalized_factors (polynomial K)
    _ _ _ _ _ _ polynomial.X f (irreducible_X) hf],
  simp only [normalize_apply, coe_norm_unit, leading_coeff_X, norm_unit_one, units.coe_one, map_one,
    mul_one, part_enat.get_coe'],
  rw count_normalized_factors_eq_count_normalized_factors_span hf X_ne_zero _ prime_X,
  { have span_ne_zero : (ideal.span {f} : ideal (polynomial K)) ≠ 0 ∧
    (ideal.span {polynomial.X} : ideal (polynomial K)) ≠ 0 := by simp only [ideal.zero_eq_bot,
    ne.def, ideal.span_singleton_eq_bot, hf, polynomial.X_ne_zero, not_false_iff, and_self],
    have span_X_prime : (ideal.span {polynomial.X} : ideal (polynomial K)).is_prime,
    { apply (@ideal.span_singleton_prime (polynomial K) _ _ polynomial.X_ne_zero).mpr prime_X },
    convert @count_normalized_factors_eq_associates_count K _ (ideal.span {f})
    (ideal.span {polynomial.X}) span_ne_zero.1 ((@ideal.span_singleton_prime (polynomial K) _ _ 
    polynomial.X_ne_zero).mpr prime_X) span_ne_zero.2 },
  { simp only [← units.coe_eq_one, coe_norm_unit, leading_coeff_X, norm_unit_one,
    units.coe_one, map_one] },
end

lemma cruciale (f : polynomial K) :
  (hahn_series.of_power_series ℕ K (↑f : power_series K)) = (↑f : hahn_series ℕ K) :=
begin
  refl,
end

example (f : polynomial K) :
  (hahn_series.of_power_series ℤ K (↑f : power_series K)) = (↑f : power_series K) :=
begin
  refl,
end


lemma order_as_nat_hahn_series_eq_int_valuation {f : polynomial K} (hf : f ≠ 0) :
 ↑(multiplicative.of_add (- (↑f : (hahn_series ℕ K)).order : ℤ)) = ((ideal_X K).int_valuation f) :=
begin
  have := order_as_power_series_eq_int_valuation K hf,
  rw hahn_series.nat_order_eq_of_power_series at this,
  rw ← this,
  simpa only [of_add_neg, of_power_series_apply, inv_inj, with_zero.coe_inj,
    embedding_like.apply_eq_iff_eq, nat.cast_inj],
end


lemma order_as_hahn_series_eq_int_valuation {f : polynomial K} (hf : f ≠ 0) :
 ↑(multiplicative.of_add (- (f : laurent_series K).order)) = ((ideal_X K).int_valuation f) :=
begin
  simp only [← order_as_nat_hahn_series_eq_int_valuation K hf, coe_coe, of_add_neg, inv_inj,
    with_zero.coe_inj, embedding_like.apply_eq_iff_eq],
  replace hf := polynomial.coe_ne_zero hf,
  erw [← hahn_series.order_eq_of_power_series_Z hf, hahn_series.nat_order_eq_of_power_series hf],
  refl,
end

variable {K}
lemma fae_order_inv {a : laurent_series K} (ha : a ≠ 0) : a⁻¹.order = - a.order :=
  by {simp only [eq_neg_iff_add_eq_zero, ← hahn_series.order_mul  (inv_ne_zero ha) ha, 
    inv_mul_cancel ha, hahn_series.order_one]}

lemma fae_order_div {a b : laurent_series K} (ha : a ≠ 0) (hb : b ≠ 0) : (a / b).order =
  a.order - b.order := 
by rwa [div_eq_mul_inv, hahn_series.order_mul ha (inv_ne_zero hb), fae_order_inv, sub_eq_add_neg]

-- `FAE` for mathlib?
lemma fae_coe (P : polynomial K) : (P : laurent_series K) = (↑P : ratfunc K) :=
  by { erw [ratfunc.coe_def, ratfunc.coe_alg_hom, lift_alg_hom_apply, ratfunc.num_algebra_map,
    ratfunc.denom_algebra_map P, map_one, div_one], refl}

-- `FAE` for mathlib?
@[simp]
lemma ratfunc.coe_ne_zero_iff {f : ratfunc K} : f ≠ 0 ↔ (↑f : laurent_series K) ≠ 0 :=
⟨λ h, by simp only [h, ne.def, algebra_map.lift_map_eq_zero_iff, not_false_iff],
  λ h, by {apply (ratfunc.coe_injective.ne_iff).mp, simpa only [ratfunc.coe_zero]}⟩

variable (K)
lemma order_as_hahn_series_eq_valuation {f : ratfunc K} (hf : f ≠ 0) :
 ↑(multiplicative.of_add (- (f : laurent_series K).order)) = ((ideal_X K).valuation f) :=
begin
  obtain ⟨P, ⟨Q, hQ, hfPQ⟩⟩ := @is_fraction_ring.div_surjective (polynomial K) _ _ (ratfunc K) _ _ _ f,
  replace hfPQ : is_localization.mk' (ratfunc K) P ⟨Q, hQ⟩ = f :=
    by simp only [hfPQ, is_fraction_ring.mk'_eq_div, set_like.coe_mk],
  have hP : P ≠ 0 :=  by {rw ← hfPQ at hf, exact is_localization.ne_zero_of_mk'_ne_zero hf},
  have hQ₀ : Q ≠ 0 := by rwa [← mem_non_zero_divisors_iff_ne_zero],
  have val_P_Q := @valuation_of_mk' (polynomial K) _ _ _ (ratfunc K) _ _ _ (ideal_X K) P ⟨Q, hQ⟩,
  rw hfPQ at val_P_Q,
  rw val_P_Q,
  simp only [← subtype.val_eq_coe],
  rw [← (order_as_hahn_series_eq_int_valuation _ hP)],
  rw [← (order_as_hahn_series_eq_int_valuation _ hQ₀)],
  rw ← with_zero.coe_div,
  rw with_zero.coe_inj,
  rw ← of_add_sub,
  replace hQ₀ : (↑Q : ratfunc K) ≠ 0,
  { exact λ hneQ, hQ₀ ((@ratfunc.algebra_map_eq_zero_iff K _ _ Q).mp hneQ) },
  apply congr_arg,
  rw neg_eq_iff_eq_neg,
  rw neg_sub_neg,
  rw neg_sub,
  rw ← fae_order_div,
  rw ← hfPQ,
  apply congr_arg,
  convert_to ↑(is_localization.mk' (ratfunc K) P ⟨Q, hQ⟩) =
  ((↑P : ratfunc K) : laurent_series K)/ (↑Q : ratfunc K) ,
  { have := ratfunc.coe_div (↑P : ratfunc K) (↑Q : ratfunc K),
    rw ← this,
    rw div_eq_iff,
    { rw fae_coe,
      rw fae_coe,
      rw ← ratfunc.coe_mul,
      apply congr_arg,
      rwa [div_mul_cancel] },
    { rwa [fae_coe, ← ratfunc.coe_ne_zero_iff] },
  },
  rw ← coe_div,
  apply congr_arg,
  simpa only [mk_eq_div, is_fraction_ring.mk'_eq_div, set_like.coe_mk],
  { intro hneP,
    have hinj := @_root_.polynomial.algebra_map_hahn_series_injective ℤ K _ _,
    exact hP ( ((@injective_iff_map_eq_zero' _ _ _ _ _ _ (_ : (polynomial K) →+*
      (laurent_series K))).mp hinj P).mp hneP),
     },
  { rwa [fae_coe, ← ratfunc.coe_ne_zero_iff], },
end

-- `FAE` Depends on `fae_order_eq_val`
lemma fae_order_eq_val' {f : ratfunc K} (hf : f ≠ 0) :
 ↑(multiplicative.of_add ((f : laurent_series K).order)) = ((ideal_X K).valuation f)⁻¹ :=
begin
  have := order_as_hahn_series_eq_valuation K (neg_ne_zero.mpr hf),
  nth_rewrite 0 [← neg_neg f],
  rw ratfunc.coe_def,
  rw (ratfunc.coe_alg_hom K).map_neg,
  rw ← ratfunc.coe_def,
  rw order_neg,
  rw of_add_neg at this,
  rw [← with_zero.coe_unzero $((ideal_X K).valuation).ne_zero_iff.mpr hf],
  rw ← with_zero.coe_inv,
  rw with_zero.coe_inj,
  rw ← inv_eq_iff_eq_inv,
  rw ← with_zero.coe_inj,
  simp only [this, with_zero.coe_unzero, valuation.map_neg],
end

namespace ratfunc

variable {K}
def coeff (f : ratfunc K) (d : ℤ) : K := (f : laurent_series K).coeff d

@[simp]
lemma coeff_zero (d : ℤ) : (0 : ratfunc K).coeff d = 0 :=
by {simp only [coeff, coe_zero], from hahn_series.zero_coeff}

variable (K)
def coeff_map (d : ℤ) : ratfunc K → K := λ x, coeff x d

lemma coeff_map_apply (d : ℤ) (f : ratfunc K) : coeff_map K d f = coeff f d := refl _

end ratfunc

lemma entourage_uniformity_mem (d : ℤ) : entourage K d ∈ 𝓤 (ratfunc K) :=
begin
  simp only [entourage, of_add_neg, with_zero.coe_inv, mem_comap, exists_prop],
  use {P | ((ideal_X K).valuation) P < (multiplicative.of_add d)⁻¹},
  split,
  { apply (@valued.mem_nhds_zero (ratfunc K) _ ℤₘ₀ _ _ _).mpr,
    use ⟨↑(multiplicative.of_add d)⁻¹, ↑(multiplicative.of_add d), by {simp only [with_zero.coe_inv,
      inv_mul_cancel, ne.def, with_zero.coe_ne_zero, not_false_iff]}, by {simp only
      [with_zero.coe_inv, _root_.mul_inv_cancel, ne.def, with_zero.coe_ne_zero, not_false_iff]}⟩,
    simp only [units.coe_mk, with_zero.coe_inv, set.set_of_subset_set_of],
    exact λ _ ha, ha },
  { simp only [set.preimage_set_of_eq, set.set_of_subset_set_of, prod.forall],
    intros _ _ h,
    rwa [← valuation.map_neg, neg_sub] },
end

variable {K}
lemma eq_coeff_of_mem_entourage {d n : ℤ} {x y : ratfunc K} (H : (x, y) ∈ (entourage K d)) :
 n ≤ d → x.coeff n = y.coeff n :=
 begin
  by_cases triv : x = y,
  { intro _,
    rw triv },
  { dsimp only [entourage] at H,
    intro hn,
    apply eq_of_sub_eq_zero,
    erw [← hahn_series.sub_coeff],
    rw [← coe_sub],
    apply hahn_series.coeff_eq_zero_of_lt_order,
    suffices : d < (↑(x - y) : laurent_series K).order,
    { exact lt_of_le_of_lt hn this },
    { rw [← multiplicative.of_add_lt, ← with_zero.coe_lt_coe,
      fae_order_eq_val' K (sub_ne_zero_of_ne triv)],
      rw [of_add_neg] at H,
      replace triv : ((ideal_X K).valuation) (x - y) ≠ 0 :=
        (valuation.ne_zero_iff _).mpr (sub_ne_zero_of_ne triv),
      rwa [← with_zero.coe_unzero triv, ← with_zero.coe_inv, with_zero.coe_lt_coe, lt_inv',
        ← with_zero.coe_lt_coe, with_zero.coe_unzero triv] }},
end

lemma eq_coeff_of_mem_entourage' {d : ℤ} {x y : ratfunc K} (H : (x, y) ∈ (entourage K d)) :
 ∀ᶠ n in at_bot, x.coeff n = y.coeff n :=
eventually_at_bot.mpr ⟨d, λ _ h, eq_coeff_of_mem_entourage H h⟩

-- example (a b c : ℤ) (h : a ≤ c -1) (H : b ≤ c) : a ≤ b - 1 :=
-- begin
--   apply h.trans,
-- end

-- `[FAE] The lemmas below are true, but possibly useless
lemma bounded_supp_of_mem_entourage (x : ratfunc K) (d : ℤ) : ∃ N : ℤ, ∀ y : ratfunc K, 
  (x, y) ∈ (entourage K d) → ∀ n ≤ N, y.coeff n = 0 :=
begin
  by_cases hx : x = 0,
  { use d,
    intros _ hy _ hn,
    rw [← eq_coeff_of_mem_entourage hy hn, hx, ratfunc.coeff_zero] },
  { replace hx := ratfunc.coe_ne_zero_iff.mp hx,
    use min ((x : laurent_series K).2.is_wf.min (hahn_series.support_nonempty_iff.mpr hx)) d - 1,
    intros _ hy _ hn,
    have hn' : x.coeff n = 0 := function.nmem_support.mp ( λ h, set.is_wf.not_lt_min
      (x : laurent_series K).2.is_wf (support_nonempty_iff.mpr hx) h _),--(lt_min_iff.mp hn).1),
    rwa ← eq_coeff_of_mem_entourage hy _,
    { exact hn.trans (le_of_lt (int.sub_one_lt_of_le (min_le_right _ _))) },
    { exact int.lt_of_le_sub_one (hn.trans (sub_le_sub (min_le_left _ _) (le_of_eq (refl _)))) }},
end

-- lemma bounded_supp_of_mem_entourage' (x : ratfunc K) (d : ℤ) : ∀ᶠ n in at_bot, ∀ y : ratfunc K, 
--   (x, y) ∈ (entourage K d) → y.coeff n = 0 :=
-- begin
--   obtain ⟨N, hN⟩ := bounded_supp_of_mem_entourage x d,
--   apply eventually_at_bot.mpr ⟨N - 1, _⟩,
--   intros n hn y hy,
--   exact hN y hy n (int.lt_of_le_sub_one hn),
-- end

lemma uniform_continuous_coeff_map {uK : uniform_space K} (h : uniformity K = 𝓟 id_rel) (d : ℤ) :
  uniform_continuous (ratfunc.coeff_map K d) :=
begin
  refine uniform_continuous_iff_eventually.mpr _,
  intros S hS,
  rw h at hS,
  refine eventually_iff_exists_mem.mpr ⟨entourage K d, ⟨entourage_uniformity_mem K d, λ x hx, hS _⟩⟩,
  exact eq_coeff_of_mem_entourage hx (le_of_eq (refl _)),
end

namespace set

lemma prod_subset_diag_singleton_left {X : Type*} [nonempty X] {S T : set X} (hS : S.nonempty)
  (hT : T.nonempty) (h_diag : S ×ˢ T ⊆ id_rel) : ∃ x, S = {x} :=
begin
  rcases ⟨hS, hT⟩ with ⟨⟨s, hs⟩, ⟨t, ht⟩⟩,
  refine ⟨s, (eq_singleton_iff_nonempty_unique_mem.mpr ⟨⟨s, hs⟩, _⟩)⟩,
  intros x hx,
  rw prod_subset_iff at h_diag,
  replace hs := h_diag s hs t ht, 
  replace hx := h_diag x hx t ht,
  simp only [id_rel, mem_set_of_eq] at hx hs,
  rwa [← hs] at hx,
end

lemma prod_subset_diag_singleton_right {X : Type*} [nonempty X] {S T : set X} (hS : S.nonempty) (hT : T.nonempty) 
  (h_diag : S ×ˢ T ⊆ id_rel) : ∃ x, T = {x} :=
begin
  rw set.prod_subset_iff at h_diag,
  replace h_diag := λ x hx y hy, (h_diag y hy x hx).symm,
  exact prod_subset_diag_singleton_left hT hS ((prod_subset_iff).mpr h_diag),
end

lemma prod_subset_diag_singleton_eq {X : Type*} [nonempty X] {S T : set X} (hS : S.nonempty) (hT : T.nonempty) 
  (h_diag : S ×ˢ T ⊆ id_rel) : ∃ x, S = {x} ∧ T = {x} :=
begin
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := ⟨prod_subset_diag_singleton_left hS hT h_diag,
    prod_subset_diag_singleton_right hS hT h_diag⟩,
  refine ⟨x, ⟨hx, _⟩⟩,
  rw [hy, set.singleton_eq_singleton_iff],
  exact (set.prod_subset_iff.mp h_diag x (by simp only [hx, set.mem_singleton]) y 
    (by simp only [hy, set.mem_singleton])).symm,
end

end set

open set

lemma cauchy_discrete_le_principal {X : Type*} [nonempty X] {uX : uniform_space X}
(hX : uniformity X = 𝓟 id_rel) {α : filter X} (hα : cauchy α) : ∃ x : X, α ≤ 𝓟 {x} :=
begin
  rcases hα with ⟨α_ne_bot, α_le⟩,
  rw [filter.le_def] at α_le,
  specialize α_le id_rel,
  simp only [filter.le_def, hX, mem_principal, id_rel_subset, mem_id_rel, eq_self_iff_true,
    implies_true_iff, forall_true_left, filter.mem_prod_iff] at α_le,
  obtain ⟨_, ⟨hS, ⟨_, ⟨hT, H⟩⟩⟩⟩ := α_le,
  obtain ⟨x, hx⟩ := prod_subset_diag_singleton_left (@filter.nonempty_of_mem X α α_ne_bot _ hS)
    (@filter.nonempty_of_mem _ _ α_ne_bot _ hT) H,
  use x,
  rwa [filter.le_principal_iff, ← hx],
end

def cauchy_discrete_is_constant {X : Type*} [nonempty X] {uX : uniform_space X}
  (hX : uniformity X = 𝓟 id_rel) {α : filter X} (hα : cauchy α) : X :=
(cauchy_discrete_le_principal hX hα).some

lemma cauchy_discrete_le  {X : Type*} [nonempty X] {uX : uniform_space X} 
  (hX : uniformity X = 𝓟 id_rel) {α : filter X} (hα : cauchy α) : 
  α ≤ 𝓟 {cauchy_discrete_is_constant hX hα} := Exists.some_spec (cauchy_discrete_le_principal hX hα)

lemma cauchy_discrete_le'  {X : Type*} [nonempty X] {uX : uniform_space X} 
  (hX : uniformity X = 𝓟 id_rel) {α : filter X} (hα : cauchy α) : 
  α ≤ 𝓝 (cauchy_discrete_is_constant hX hα) :=
begin
  convert cauchy_discrete_le hX hα,
  have top_discrete : ∀ a : X, is_open {a},
    { exact λ a, @is_open_discrete _ _ (discrete_topology_of_discrete_uniformity hX) {a} },
  rw [((is_open_singleton_iff_nhds_eq_pure _).mp (top_discrete _)), principal_singleton],
end

lemma ne_bot_unique_principal {X : Type*} [uniform_space X] (hX : uniformity X = 𝓟 id_rel)
  {α : filter X} (hα : α.ne_bot) {x y : X} (hx : α ≤ 𝓟 {x}) (hy : α ≤ 𝓟 {y}) : x = y :=
begin
  have h_disc : discrete_topology X,
  apply discrete_topology_of_discrete_uniformity hX,
  have t2X := @discrete_topology.to_t2_space X _ h_disc,
  apply @eq_of_nhds_ne_bot X _ t2X x y,
  simp only [discrete_topology_iff_nhds.mp h_disc],
  apply @ne_bot_of_le _ _ _ hα,
  simp only [le_inf_iff, le_pure_iff],
  exact ⟨le_principal_iff.mp hx, le_principal_iff.mp hy⟩,
end

/- The definition below avoids the assumption that `K` be endowed with the trivial uniformity,
  rather putting this in the proof.
-/
def cauchy.coeff_map {ℱ : filter (ratfunc K)} (hℱ : cauchy ℱ) : ℤ → K :=
begin
  letI : uniform_space K := ⊥,
  have hK : @uniformity K ⊥ = filter.principal id_rel := rfl,
  use λ d, (cauchy_discrete_is_constant hK (hℱ.map (uniform_continuous_coeff_map hK d))),
end

def Cauchy.coeff_map (d : ℤ) : Cauchy (ratfunc K) → K :=
begin
  letI : uniform_space K := ⊥,
  have hK : @uniformity K ⊥ = filter.principal id_rel := rfl,
  use λ ℱ, (cauchy_discrete_is_constant hK (ℱ.2.map (uniform_continuous_coeff_map hK d))),
end

def Cauchy.coeff_map' {uK : uniform_space K} (h : uniformity K = 𝓟 id_rel) (d : ℤ) :
  Cauchy (ratfunc K) → K := Cauchy.extend (ratfunc.coeff_map K d)


/-To perform explicit computation, `Cauchy.coeff_map` is more suitable, but `Cauchy.coeff_map'` is
defined in a way that unveils its abstract properties better.-/
lemma coeff_map_eq_coeff_map' {uK : uniform_space K} (h : uniformity K = 𝓟 id_rel) (d : ℤ) :
  Cauchy.coeff_map d = Cauchy.coeff_map' h d :=
begin
  haveI t2_K : t2_space K, sorry,
  have top_discrete : ∀ a : K, is_open {a},
    { exact λ a, @is_open_discrete _ _ (discrete_topology_of_discrete_uniformity h) {a} },
  ext ℱ,
  have ℱ_bot : (comap (@Cauchy.pure_cauchy (ratfunc K) _) (𝓟 {ℱ})).ne_bot,
  {sorry},
  simp only [Cauchy.coeff_map, Cauchy.coeff_map', Cauchy.extend,
    if_pos (uniform_continuous_coeff_map h d), subtype.val_eq_coe],
  -- have due : lim (filter.comap Cauchy.pure_cauchy (𝓝 ℱ)) (ratfunc.coeff_map K d) =
  --   (cauchy_discrete_is_constant h (ℱ.2.map (uniform_continuous_coeff_map h d))),
  have speroma : comap Cauchy.pure_cauchy (𝓟 {ℱ}) = ℱ.1, sorry,
  have uno : lim (filter.comap Cauchy.pure_cauchy (𝓟 {ℱ})) (ratfunc.coeff_map K d) =
    (cauchy_discrete_is_constant h (ℱ.2.map (uniform_continuous_coeff_map h d))),
    { rw [lim, Lim_eq_iff _],
      rw speroma,
      apply cauchy_discrete_le',
      exact t2_K,
      simp [ℱ_bot], sorry,
      use ℱ.coeff_map d,
      rw speroma,
      simp,
      rw Cauchy.coeff_map,
      simp,
      -- apply cauchy_discrete_le',
    },
    -- { rw [lim, Lim_eq_iff _],
    --   -- rw [Lim_eq_iff _],
    --   { rw ((is_open_singleton_iff_nhds_eq_pure _).mp (top_discrete _)),
    --     rw ← principal_singleton,
    --     apply le_trans _ (cauchy_discrete_le h (ℱ.2.map (uniform_continuous_coeff_map h d))),
    --     apply filter.map_mono,
    --     -- simp only [principal_singleton, subtype.val_eq_coe],
    --     intros T hT,
    --     rw mem_comap,
    --     -- use set.Iic (𝓟 {ℱ}),
    --     -- use {ℱ},
    --     -- split,
    --     -- sorry,
    --     -- rw mem_nh
    --     -- rw mem_nhds_iff,
    --     -- rw filter.mem_principal,
    --     rw set.preimage_subset_iff,
    --     intro f,
    --     -- intro f,
    --     rw Cauchy.pure_cauchy,
    --     intro hf,
    --     rw mem_singleton_iff at hf,
    --     rw subtype.ext_iff at hf,
    --     rw [← hf, subtype.coe_mk, mem_pure] at hT,
    --     -- exact hT,
    --   },
      { rw ((is_open_singleton_iff_nhds_eq_pure _).mp (top_discrete _)),
        rw ← principal_singleton,
        apply le_trans _ (cauchy_discrete_le h (ℱ.2.map (uniform_continuous_coeff_map h d))),
        apply filter.map_mono,
        simp only [principal_singleton, comap_pure, subtype.val_eq_coe],
        intros T hT,
        rw filter.mem_principal,
        rw set.preimage_subset_iff,
        intro f,
        rw Cauchy.pure_cauchy,
        intro hf,
        rw mem_singleton_iff at hf,
        rw subtype.ext_iff at hf,
        rw [← hf, subtype.coe_mk, mem_pure] at hT,
        exact hT,
      },
      { exact t2_K},
      { sorry },
      { use cauchy_discrete_is_constant h (ℱ.2.map (uniform_continuous_coeff_map h d)),
        apply le_trans _ (cauchy_discrete_le' h (ℱ.2.map (uniform_continuous_coeff_map h d))),
        apply filter.map_mono,
        simp only [principal_singleton, comap_pure, subtype.val_eq_coe],
        intros T hT,
        rw filter.mem_principal,
        rw set.preimage_subset_iff,
        intro f,
        rw Cauchy.pure_cauchy,
        intro hf,
        rw mem_singleton_iff at hf,
        rw subtype.ext_iff at hf,
        rw [← hf, subtype.coe_mk, mem_pure] at hT,
        exact hT, }},

      -- convert uno.symm,
      -- sorry,
      -- dsimp [Cauchy.dense_inducing_pure_cauchy.extend],
      erw ← uno,
      -- rw principal_singleton,
      rw dense_inducing.extend,
      symmetry,
      rw @lim_eq_iff _ _ _ _ _ _,
      sorry,
      sorry,
      sorry,
      sorry, 
      -- rw @lim_eq_iff _ _ _ _ _ ℱ_bot, 
      -- rw lim_monoto
      -- rw lim,
      -- rw Lim,
      -- simp,
      -- simp,
      -- congr' 1,

      
      
      -- exact (is_open_singleton_iff_nhds_eq_pure _).mp (top_discrete _),


end

lemma Cauchy.uniform_continuous_coeff_map {uK : uniform_space K} (h : uniformity K = 𝓟 id_rel)
  (d : ℤ) : uniform_continuous (Cauchy.coeff_map' h d) :=
begin
  haveI hK_compl : complete_space K,
  { rw complete_space_iff_ultrafilter,
    intros ℱ hℱ,
    set a := cauchy_discrete_is_constant h hℱ with ha,
    have top_discrete : is_open {a},
    { exact @is_open_discrete _ _ (discrete_topology_of_discrete_uniformity h) {a} },
    use a,
    convert cauchy_discrete_le h hℱ,
    rw principal_singleton,
    exact (is_open_singleton_iff_nhds_eq_pure a).mp top_discrete},
  apply Cauchy.uniform_continuous_extend,
end

/- Lemma below needed for the trivial generalization `Cauchy.laurent_series_eq_of_inseparable`-/
lemma Cauchy.coeff_eq_of_inseparable (d : ℤ)  (ℱ 𝒢 : Cauchy (ratfunc K)) 
(H : (ℱ, 𝒢) ∈ separation_rel (Cauchy (ratfunc K))) : ℱ.coeff_map d = 𝒢.coeff_map d :=
begin
  letI : uniform_space K := ⊥,
  have hK : @uniformity K ⊥ = filter.principal id_rel := rfl,
  haveI : separated_space K,
  { rw [separated_space_iff, separation_rel, hK],
    ext x,
    simp only [mem_sInter, filter.mem_sets, mem_principal, id_rel_subset],
    split,
    { intro hx,
      simp only [hx, mem_id_rel, eq_self_iff_true, forall_const]},
    {intros hx T hT,
      simp [hx, ← id_rel_subset] at hT,
      exact hT hx}},
  rw coeff_map_eq_coeff_map',
  exact uniform_space.eq_of_separated_of_uniform_continuous
    (Cauchy.uniform_continuous_coeff_map hK d) H,
end

@[simp]
lemma cauchy.coeff_map_le {ℱ : filter (ratfunc K)} (hℱ : cauchy ℱ) (n : ℤ) : 
  ℱ.map (ratfunc.coeff_map K n) ≤ 𝓟 {hℱ.coeff_map n} := 
begin
  letI : uniform_space K := ⊥,
  have hK : uniformity K = filter.principal id_rel, refl,
  exact cauchy_discrete_le _ _,
end

@[simp]
lemma Cauchy.coeff_map_le (ℱ : Cauchy (ratfunc K)) (n : ℤ) : 
  ℱ.1.map (ratfunc.coeff_map K n) ≤ 𝓟 {ℱ.coeff_map n} := 
begin
  letI : uniform_space K := ⊥,
  have hK : uniformity K = filter.principal id_rel, refl,
  exact cauchy_discrete_le _ _,
end

-- example : uniform_continuous₂ (λ f g : (ratfunc K), f + g ) :=
-- begin
--   rw uniform_continuous₂_def,
--   apply uniform_continuous_add,
-- end


lemma coeff_eventually_zero_cauchy {ℱ : filter (ratfunc K)} (hℱ : cauchy ℱ) : ∃ N, 
  ∀ᶠ y in ℱ, ∀ n ≤ N, ratfunc.coeff y n = (0 : K) :=
begin
  obtain ⟨S, ⟨hS, ⟨T, ⟨hT, H⟩⟩⟩⟩ := filter.mem_prod_iff.mp (filter.le_def.mp hℱ.2 (entourage K 0)
    (entourage_uniformity_mem _ _)),
  obtain ⟨x, hx⟩ := filter.forall_mem_nonempty_iff_ne_bot.mpr hℱ.1 (S ∩ T)
    (by {exact inter_mem_iff.mpr ⟨hS, hT⟩}),
  obtain ⟨N, hN⟩ := bounded_supp_of_mem_entourage x 0,
  use N,
  rw filter.eventually,
  apply mem_of_superset (inter_mem hS hT),
  suffices : (S ∩ T) ×ˢ (S ∩ T) ⊆ entourage K 0,
  { intros y hy,
    have h_prod : (x, y) ∈ entourage K 0,
    { refine this (mem_prod.mpr _),
      exact ⟨hx, hy⟩ },
    exact hN y h_prod },
  exact (prod_mono (inter_subset_left S T) (inter_subset_right S T)).trans H,
end

lemma cauchy.coeff_map_zero_at_bot {ℱ : filter (ratfunc K)} (hℱ : cauchy ℱ) : ∃ N, 
  ∀ n ≤ N, ℱ.map (ratfunc.coeff_map K n) ≤ filter.principal {0} :=
begin
  simp only [principal_singleton, pure_zero, nonpos_iff, mem_map],
  obtain ⟨N, hN⟩ := coeff_eventually_zero_cauchy hℱ,
  use  N,
  intros n hn,
  apply filter.mem_of_superset hN,
  intros a ha,
  exact ha n hn,
end

lemma cauchy.coeff_map_zero_at_bot' {ℱ : filter (ratfunc K)} (hℱ : cauchy ℱ) : ∀ᶠ n in at_bot,
  ℱ.map (ratfunc.coeff_map K n) ≤ filter.principal {0} :=
eventually_at_bot.mpr (cauchy.coeff_map_zero_at_bot hℱ)
  
-- lemma cauchy.coeff_map_zero_at_bot'' {ℱ : filter (ratfunc K)} (hℱ : cauchy ℱ) : ∀ᶠ n in at_bot,
--   hℱ.coeff_map n = 0 :=
-- begin
--   have := hℱ.coeff_map_zero_at_bot,
--   simp only [principal_singleton, pure_zero, nonpos_iff, mem_map] at this,
--   -- simp,
-- end

lemma cauchy.coeff_map_support_bdd {ℱ : filter (ratfunc K)} (hℱ : cauchy ℱ) : ∃ N, ∀ n,
  n ≤ N → (hℱ.coeff_map n) = 0 :=
begin
  letI : uniform_space K := ⊥,
  have hK : uniformity K = filter.principal id_rel, refl,
  obtain ⟨N, hN⟩ := hℱ.coeff_map_zero_at_bot,
  use N,
  intros n hn,
  exact ne_bot_unique_principal hK (hℱ.map (uniform_continuous_coeff_map hK n)).1
    (hℱ.coeff_map_le n) (hN n hn),
end

lemma cauchy.coeff_map_support_bdd' {ℱ : filter (ratfunc K)} (hℱ : cauchy ℱ) :
  bdd_below (hℱ.coeff_map.support) :=
begin
  obtain ⟨N, hN⟩ := hℱ.coeff_map_support_bdd,
  use N,
  intros n hn,
  rw function.mem_support at hn,
  contrapose! hn,
  exact hN _ (le_of_lt hn),
end

lemma Cauchy.coeff_map_support_bdd (ℱ : Cauchy (ratfunc K)) :
  bdd_below ((λ d, ℱ.coeff_map d).support) :=
begin
  obtain ⟨N, hN⟩ := ℱ.2.coeff_map_support_bdd,
  use N,
  intros n hn,
  rw function.mem_support at hn,
  contrapose! hn,
  exact hN _ (le_of_lt hn),
end

-- lemma eventually_constant {uK : uniform_space K} (h : uniformity K = 𝓟 id_rel)
--   {ℱ : filter (ratfunc K)} (hℱ : cauchy ℱ) (n : ℤ) :
--   ∀ᶠ x in ℱ, ratfunc.coeff x n = cauchy_discrete_is_constant h 
--     (hℱ.map (uniform_continuous_coeff_map h n)) := by simpa only [comap_principal, le_principal_iff]
--     using tendsto.le_comap (cauchy_discrete_converges _ (hℱ.map (uniform_continuous_coeff_map _ _)))


-- lemma coeff_entually_zero {uK : uniform_space K} (h : uniformity K = 𝓟 id_rel)
--   {ℱ : filter (ratfunc K)} (hℱ : cauchy ℱ) :
--   ∀ᶠ x in ℱ, ∀ᶠ d in (at_bot : filter ℤ), ratfunc.coeff x d = (0 : K) :=
-- begin
--   simp only [eventually_at_bot],
--   apply eventually_of_forall,
--   intro x,
--   by_cases hx : x = 0,
--   { simp only [hx, ratfunc.coeff_zero, eq_self_iff_true, implies_true_iff, exists_const] },
--   { replace hx := ratfunc.coe_ne_zero_iff.mp hx, 
--     use ((x : laurent_series K).2.is_wf.min (hahn_series.support_nonempty_iff.mpr
--     hx)) - 1,
--     intros,
--     apply function.nmem_support.mp ( λ h, set.is_wf.not_lt_min
--       (x : laurent_series K).2.is_wf (support_nonempty_iff.mpr hx) h _),
--     linarith },
-- end

-- lemma support_bdd_below {uK : uniform_space K} (h : uniformity K = 𝓟 id_rel)
--   {ℱ : filter (ratfunc K)} (hℱ : cauchy ℱ) : support coeff_map := sorry

-- #check λ d : ℤ, filter.map (ratfunc.coeff d)

-- `[FAE]` This is `#18604`
lemma bdd_below.well_founded_on_lt {X : Type} [preorder X] {s : set X} : 
  bdd_below s → s.well_founded_on (<) := sorry


def Cauchy.to_laurent_series (ℱ : Cauchy (ratfunc K)) : (laurent_series K) :=
hahn_series.mk (λ d, ℱ.coeff_map d) (is_wf.is_pwo ℱ.coeff_map_support_bdd.well_founded_on_lt)

variable (K)
/-- The lemma `Cauchy.laurent_series_eq_of_inseparable` guarantees that if two filters are "closed"
  the Laurent series that they give rise to coincide. This is needed to `lift` functions defined
  on the `completion`=`Cauchy/(inseparables)`, and ultimately to define
  `laurent_series.equiv_other_proof.to_fun` as a function leaving from the completion rather than
  from `Cauchy`.
-/

lemma Cauchy.laurent_series_eq_of_inseparable (ℱ 𝒢 : Cauchy (ratfunc K)) 
(H : (ℱ, 𝒢) ∈ separation_rel (Cauchy (ratfunc K))) : ℱ.to_laurent_series = 𝒢.to_laurent_series :=
begin
  simp [Cauchy.to_laurent_series, Cauchy.coeff_eq_of_inseparable _ _ _ H],
end

section truncation
open ideal

variable {K}
-- def laurent_series.X_pow (f : laurent_series K) (hf : f ≠ 0) : ℤ := 
-- (away.exists_reduced_fraction (power_series.X : (power_series K)) (laurent_series K)
--   power_series.irreducible_X f hf).some_spec.some

-- def laurent_series.power_series_part (f : laurent_series K) (hf : f ≠ 0) : ℤ := 
-- (exists_reduced_fraction (power_series.X : (power_series K)) (laurent_series K)
--   power_series.irreducible_X f hf).some_spec.some

-- def laurent_series.trunc' (f : laurent_series K) (d : ℕ) : ratfunc K :=
-- if hf : f = 0 then 0 else
-- begin
--   let F := (away.exists_reduced_fraction (power_series.X : (power_series K)) (laurent_series K)
--     power_series.irreducible_X f hf).some,
--   use (ratfunc.X : (ratfunc K))^(f.X_pow hf) * ↑(F.trunc d),
-- end

def laurent_series.trunc (f : laurent_series K) (d : ℕ) : ratfunc K :=
if hf : f = 0 then 0 else ratfunc.X^(f.order) * ↑((power_series_part f).trunc d)

lemma trunc_coeff_eq_zero_of_lt (f : laurent_series K) {d n: ℕ} (h : n < d) :
  ((power_series_part f).trunc d).coeff n = 0 :=
begin
  sorry,
end

lemma trunc_coeff_eq_coeff_of_ge (f : laurent_series K) {d n: ℕ} (h : d ≤ n) :
  ((power_series_part f).trunc d).coeff n = 0 := sorry

lemma int_valuation_trunc_sub (f : laurent_series K) {d₁ d₂ : ℕ} (hd : d₁ ≤ d₂) :
  (ideal_X K).int_valuation ((power_series_part f).trunc d₂ - (power_series_part f).trunc d₁)
    ≤ ↑(multiplicative.of_add (- (d₁ : ℤ))) :=
begin
  set g := (power_series_part f).trunc d₂ - (power_series_part f).trunc d₁ with hg,
  by_cases H : g ≠ 0,
  { have h_coeff : polynomial.X ^ d₁ ∣ g,
    { rw polynomial.X_pow_dvd_iff,
      intros m hm,
      rw [coeff_sub, trunc_coeff_eq_zero_of_lt f hm, trunc_coeff_eq_zero_of_lt f
        (lt_of_lt_of_le hm hd), zero_sub_zero]},
  rwa [← hg, fae_int_valuation_apply, int_valuation_le_pow_iff_dvd, ideal_X_span,
    dvd_span_singleton, span_singleton_pow, mem_span_singleton] },
  { simp only [← hg, not_not.mp H, valuation.map_zero, zero_le'] }
end

lemma valuation_trunc_sub {f : laurent_series K} (hf : f ≠ 0) {d₁ d₂ : ℕ} (hd : d₁ ≤ d₂) :
  (ideal_X K).valuation ((f.trunc d₂ - f.trunc d₁))
    ≤ ↑(multiplicative.of_add (- f.order - d₁ : ℤ)) :=
begin
  simp only [laurent_series.trunc, dif_neg hf, ← mul_sub, valuation.map_mul, map_zpow₀, of_add_sub,
    with_zero.coe_div, val_X_eq_one, ← with_zero.coe_zpow, ← of_add_zsmul, zsmul_neg, zsmul_one,
    int.cast_id, div_eq_mul_inv, ← with_zero.coe_inv, ← of_add_neg],
  simp only [sub_eq_add_neg, ← algebra_map.coe_neg, ← algebra_map.coe_add],
  convert (mul_le_mul_left₀ _).mpr (int_valuation_trunc_sub f hd),
  convert @valuation_of_algebra_map (polynomial K) _ _ _ (ratfunc K) _ _ _ (ideal_X K)
   (power_series.trunc d₂ f.power_series_part - power_series.trunc d₁ f.power_series_part),
  apply with_zero.coe_ne_zero,
end

definition truncation_seq (f : laurent_series K) : ℕ → ratfunc K := λ d, f.trunc d

@[simp]
lemma truncation_zero : truncation_seq (0 : (laurent_series K)) = 0 :=
  by simp only [truncation_seq, laurent_series.trunc, dif_pos, function.const_eq_zero]


-- lemma trunc_same_denom (f : laurent_series K) (d₁ d₂ : ℕ) :
--   (f.trunc d₁).denom = (f.trunc d₂).denom :=
-- begin
--   sorry,
-- end

-- lemma no_denom_if_Xpow_nonneg (f : laurent_series K) (hf : f ≠ 0) (hX : 0 ≤ (f.X_pow hf)) (d : ℕ) : 
--   (f.trunc d).denom = 1 :=
-- begin
--   sorry
-- end

-- lemma sub_trunc (f : laurent_series K) (d₁ d₂ : ℕ) (hd : d₁ ≤ d₂) : 
--   polynomial.X^d₁ ∣ (f.trunc d₁ - f.trunc d₂).num := sorry

-- lemma laurent_series_trunc_eq_power_series (f : power_series K) (d : ℕ) : 
--   (f : laurent_series K).trunc d = ↑(f.trunc d) := sorry


theorem truncation_cauchy_seq (f : laurent_series K) : cauchy_seq (truncation_seq f) :=
begin
  by_cases hf : f = 0,  
  { convert @cauchy_seq_const _ ℕ _ _ _ (0 : ratfunc K),
    funext,
    simp only [hf, truncation_zero, pi.zero_apply], },
  { simp_rw has_basis.cauchy_seq_iff (valued.has_basis_uniformity (ratfunc K) ℤₘ₀),
    rintros i -,
    obtain ⟨j, hj⟩ := with_zero.ne_zero_iff_exists.mp (units.ne_zero i),
    simp only [ge_iff_le, mem_set_of_eq, truncation_seq],
    use int.nat_abs (-f.order - j) + 1,
    intros m hm n hn,
    wlog hmn : m ≤ n with Hsymm,
    { convert Hsymm f hf i j hj _ hn _ hm (le_of_not_ge hmn) using 1,
      suffices : f.trunc n - f.trunc m = - (f.trunc m - f.trunc n),
      rw [this, valuation.map_neg],
      ring },
    { replace hm : - f.order - j < m,
      { refine lt_of_le_of_lt int.le_nat_abs (nat.cast_lt.mpr (nat.lt_of_succ_le (le_trans _ hm))),
        rw nat.succ_eq_add_one},
      apply lt_of_le_of_lt (valuation_trunc_sub hf hmn),
      rw [← hj, with_zero.coe_lt_coe],
      exact sub_lt_comm.mp hm }},
end

def truncation_cauchy_filter (f : laurent_series K) : Cauchy (ratfunc K) := 
  ⟨at_top.map (truncation_seq f), truncation_cauchy_seq f⟩

lemma truncation_coeff_eq_coeff (f : laurent_series K) (d : ℤ) : 
 (truncation_cauchy_filter f).2.coeff_map d = f.coeff d :=
begin
  sorry,
end

end truncation

def laurent_series.equiv_other_proof : (completion_of_ratfunc K) ≃ (laurent_series K) :=
{ to_fun := λ α, quot.lift Cauchy.to_laurent_series (Cauchy.laurent_series_eq_of_inseparable K) α,
  inv_fun := λ f, quotient.mk' $ truncation_cauchy_filter f,
  left_inv := 
  begin
    rw function.left_inverse,
    rintro ⟨α, hα⟩,
    simp,
    have : truncation_cauchy_filter (Cauchy.to_laurent_series ⟨α, hα⟩) = ⟨α, hα⟩,
    { ext,
      sorry,
    
    },
    rw this,
    rw quotient.mk',
  end,
  right_inv := λ f, hahn_series.ext _ _ (_root_.funext (λ _, truncation_coeff_eq_coeff _ _))
   }
  
    -- apply equiv.of_bijective
  --   (λ α, quot.lift Cauchy.to_laurent_series (Cauchy.laurent_series_eq_of_inseparable K) α),
  -- simp,
  -- sorry

#exit

variable {K}
def laurent_series.equiv : (completion_of_ratfunc K) ≃ (laurent_series K) :=
{ to_fun :=
  begin
    intro α,
    obtain ⟨ℱ, hℱ⟩ := (quot.exists_rep α).some,
    apply hahn_series.mk,
    exact is_wf.is_pwo ((hℱ.coeff_map_support_bdd').well_founded_on_lt),
  end,
  inv_fun := -- apply cau_seq.completion.mk_add-- there are a lot of things like this, only useful for
    -- valued fields, but the proofs are probably exactly what I need
    -- λ f, @quotient.mk (Cauchy (ratfunc K)) (uniform_space.separation_setoid _)
    --   ⟨at_top.map (truncation_seq f), truncation_cauchy_seq f⟩,
    -- begin
      λ f, quotient.mk' $ truncation_cauchy_filter f,

    -- end,
  left_inv := 
  begin
    intro ℱ,
    simp only,
    sorry,
  end,
  -- sorry,
  right_inv := 
  begin
    intro f,
    ext d,
    simp,
    have := truncation_coeff_eq_coeff f d,
    rw ← this,
    rw ← truncation_coeff_eq_coeff,
    congr,
    sorry,
    -- simp,
    -- simp,
  end, }

example {ℱ ℱ' : filter (ratfunc K)} (hℱ : cauchy ℱ) (hℱ' : cauchy ℱ') :
  cauchy ((ℱ.prod ℱ').map (+).uncurry) := 
begin
  exact (hℱ.prod hℱ').map (uniform_continuous_add),
end

lemma coeff_map_add {ℱ ℱ' : filter (ratfunc K)} (hℱ : cauchy ℱ) (hℱ' : cauchy ℱ') :
  ((hℱ.prod hℱ').map (uniform_continuous_add)).coeff_map = hℱ.coeff_map + hℱ'.coeff_map :=
begin
  ext n,
  -- have fine : ((ℱ.prod ℱ').map (+).uncurry).coeff_map n ≤ 𝓝 ( (hℱ.coeff_map n) + (hℱ'.coeff_map n)),
  -- letI : uniform_space K := ⊥,
  
  rw cauchy.coeff_map,
  rw cauchy.coeff_map,
  rw cauchy.coeff_map,
  simp,
  sorry
end

noncomputable! def laurent_series.ring_equiv : 
  ring_equiv (completion_of_ratfunc K) (laurent_series K) :=
{ map_mul' := sorry,
  map_add' := sorry,
  .. laurent_series.equiv }

#where
noncomputable! def power_series.ring_equiv : ring_equiv (adic_completion_integers (ratfunc K) 
  (ideal_X K : is_dedekind_domain.height_one_spectrum (polynomial K))) (power_series K) :=
sorry

instance : algebra (ratfunc K) (completion_of_ratfunc K) := 
adic_completion.algebra (polynomial K) (ratfunc K) (ideal_X K)

instance completion_of_ratfunc.K_algebra : algebra K (completion_of_ratfunc K) := 
algebra.comp K (ratfunc K) (completion_of_ratfunc K)

noncomputable! def laurent_series.alg_equiv : 
  alg_equiv K (completion_of_ratfunc K) (laurent_series K) :=
{ to_fun    := laurent_series.equiv.to_fun,
  inv_fun   := laurent_series.equiv.inv_fun,
  map_mul'  := sorry,
  map_add'  := sorry,
  commutes' := sorry,
  ..(laurent_series.equiv) }

/- **OLD THINGS** 

  -- is_dedekind_domain.height_one_spectrum.uniform_space_adic_completion (ratfunc K) _

-- lemma foo : (nhds (0 : ratfunc K)).has_basis set.univ (λ n : ℕ,
--   {F : (ratfunc K) | ↑(multiplicative.of_add (n : ℤ)) ≤ (ideal_X K).valuation F}) :=
-- begin
--   sorry
-- end

-- lemma foo' : (nhds (0 : ratfunc K)).has_basis set.univ (λ n : ℤ,
--   {F : (ratfunc K) | ↑(multiplicative.of_add n) ≤ (ideal_X K).valuation F}) :=
-- begin
--   sorry
-- end

-- def boo := filter.has_basis.uniformity_of_nhds_zero (foo K)

-- #check boo K

-- lemma boo_subset (n : ℕ) : (boo K n) ∈ (𝓤 (ratfunc K)) :=
-- variable (d : ℤ)
-- #check foo K

-- lemma uff : true := sorry
-- include K F

-- def ss (F : completion_of_ratfunc K) : ℕ → (ratfunc K) := seq ((quot.exists_rep F).some).2
--     (λ n, @filter.has_basis.mem_of_mem _ _ _ _ _ n
--     (filter.has_basis.uniformity_of_nhds_zero (foo K)) trivial)

  -- is_dedekind_domain.height_one_spectrum.uniform_space_adic_completion (ratfunc K) _

-- lemma foo : (nhds (0 : ratfunc K)).has_basis set.univ (λ n : ℕ,
--   {F : (ratfunc K) | ↑(multiplicative.of_add (n : ℤ)) ≤ (ideal_X K).valuation F}) :=
-- begin
--   sorry
-- end

-- lemma foo' : (nhds (0 : ratfunc K)).has_basis set.univ (λ n : ℤ,
--   {F : (ratfunc K) | ↑(multiplicative.of_add n) ≤ (ideal_X K).valuation F}) :=
-- begin
--   sorry
-- end

-- def boo := filter.has_basis.uniformity_of_nhds_zero (foo K)

-- #check boo K

-- lemma boo_subset (n : ℕ) : (boo K n) ∈ (𝓤 (ratfunc K)) :=
-- variable (d : ℤ)
-- #check foo K

-- lemma uff : true := sorry
-- include K F

-- def ss (F : completion_of_ratfunc K) : ℕ → (ratfunc K) := seq ((quot.exists_rep F).some).2
--     (λ n, @filter.has_basis.mem_of_mem _ _ _ _ _ n
--     (filter.has_basis.uniformity_of_nhds_zero (foo K)) trivial)

-- #check ss K F
-- --   use this,
-- -- end
-- -- #check @filter.has_basis.mem_of_mem (ratfunc K) ℕ (nhds 0) (λ n, true) _ d (foo K)

-- -- #check boo

-- lemma boo_subset (n : ℕ) : (boo K n) ∈ (𝓤 (ratfunc K)) :=

-- def entourage : ℕ → set ((ratfunc K) × (ratfunc K)):= λ n,
--   {x | ↑(multiplicative.of_add (n : ℤ)) ≤ ((ideal_X K).valuation x) } ×ˢ
--   { x | ↑(multiplicative.of_add (n : ℤ)) ≤ ((ideal_X K).valuation x) }

-- example : add_group (ratfunc K) := 
-- begin
--   apply_instance,
-- end

-- -- local attribute [instance] topological_add_group.to_uniform_add_group


-- example (G : Type*) [_inst_1 : add_group G] [_inst_2 : topological_space G] [_inst_3 : topological_add_group G] :
--     𝓤 G = filter.comap (λ (p : G × G), p.snd - p.fst) (nhds 0) :=
-- begin
--   apply uniformity_eq_comap_nhds_zero',
-- end

-- lemma entourage_subset (n : ℕ) : entourage K n ∈ (𝓤 (ratfunc K)) :=
-- begin
--   rw uniformity_eq_comap_nhds_zero' (ratfunc K),
--   rw filter.mem_comap',
--   rw entourage,
--   simp,
--   rw mem_nhds_iff,
--   use {F : (ratfunc K) | ↑(multiplicative.of_add (n : ℤ)) ≤ (ideal_X K).valuation F},
--   split,
--   { simp only [set.set_of_subset_set_of],


--   },





  -- intro,
    -- have one : is_open ({y :
  --  ratfunc K | ∀ (a b : ratfunc K),
  --  b - a = y → (multiplicative.of_add (n : ℤ)) ≤ ((ideal_X K).valuation) a ∧
  --    (multiplicative.of_add (n : ℤ)) ≤ ((ideal_X K).valuation) b}),
  --     sorry,
  
-- end

-- #check seq ((quot.exists_rep F).some).2 (entourage_subset K)

-- def ss_int : ℤ → laurent_series K
-- |(n : nat) := ss K F n
-- | _ := 0

-- lemma foo2 (α : Type*) (u : ℕ → α) (N : ℕ) (hu : ∀ m : ℕ, N ≤ m → u m = u N) :
--   at_top.map u ≤ pure (u N) := --at_top.map u ≤ 𝓟 ({u N}) :=
-- begin
--   simp only [le_pure_iff, mem_map, mem_at_top_sets, ge_iff_le, set.mem_preimage,
--     set.mem_singleton_iff],
--   exact ⟨N, hu⟩,
-- end

-- lemma bar (α : Type*) (u : ℕ → α) (N : ℕ) (H : at_top.map u ≤ pure (u N)) :
--   ∃ d, ∀ m : ℕ, d ≤ m → u m = u d :=
--   --  := --at_top.map u ≤ 𝓟 ({u N}) :=
-- begin
--   -- intros m hm,
--   -- simp only [le_pure_iff, mem_map, mem_at_top_sets, ge_iff_le, set.mem_preimage,
--   --   set.mem_singleton_iff] at H,
--   simp at H,
--   obtain ⟨a, ha⟩ := H,
--   use a,
--   intros m hm,
--   by_cases a ≤ N,
--   { have : u a = u N,
--     exact ha a (le_of_eq (refl _)),
--     rw this,
--     exact ha _ hm },
--   { replace h : N < a, sorry, sorry,  },
--   -- let A := min a N,
--   -- have hm' : A ≤ m,
--   -- simp * at *,
--   -- apply ha,
--   -- have := (le_of_eq (refl a)),
--   -- specialize ha b (le_max_iff.mpr _),
--   -- apply or.intro_left _, 
--   -- exact this,
  
--   -- simp only [this, true_or],
--   -- have := (true_or (le_of_eq (refl a))),

--   -- squeeze_simp [b],
--   -- simp only [le_pure_iff, mem_map, mem_at_top_sets, ge_iff_le, set.mem_preimage,
--   --   set.mem_singleton_iff],
--   -- exact ⟨N, hu⟩,
-- end

-- def eventual_coeff (ℱ : filter (ratfunc K)) (h : cauchy ℱ) (d : ℤ) : K :=
-- -- ∃ (t : set (laurent_series K)), t ∈ ℱ.map (ratfunc.coe_alg_hom K) ∧ t ≠ ∅ ∧ (∀ F G : (laurent_series K), F ∈ t → G ∈ t → F.coeff d = G.coeff d),
--   sorry

-- def temp_coeff : ℤ → (laurent_series K → K) := λ i F, F.coeff i

-- lemma eventually_eq_eventual_coeff (ℱ : filter (ratfunc K)) (h : cauchy ℱ) (d : ℤ) :
--   -- ( T : set (completion_of_ratfunc K)) : 
--   ∀ T ∈ ℱ, (ℱ.map (ratfunc.coe_alg_hom K)).map (temp_coeff K d) = (ℱ.map (ratfunc.coe_alg_hom K)).map (temp_coeff K d) :=
-- begin
--   sorry,
-- end

-- example (X : Type*) [uniform_space X] (ℱ : filter X) (hF : cauchy ℱ) :
--   ∃ x : uniform_space.completion X, ℱ.map coe ≤ 𝓝 x :=
-- begin
--   refine complete_space.complete _,
--   refine cauchy.map hF _,
--   refine uniform_space.completion.uniform_continuous_coe X,
-- end

-- variable [decidable_rel (has_dvd.dvd : (polynomial K) → (polynomial K) → Prop)]
-- variable [decidable_rel (has_dvd.dvd : (power_series K) → (power_series K) → Prop)]

-- lemma multiplicity_pol_eq_multiplicity_power_series {f : polynomial K} (hf :f ≠ 0) :
--   multiplicity power_series.X (↑f : power_series K) = multiplicity polynomial.X f :=
-- begin
--   sorry,
-- end


-- -- variable [decidable_rel (has_dvd.dvd : (hahn_series ℕ K) → (hahn_series ℕ K) → Prop)]

-- -- lemma multiplicity_pol_eq_multiplicity_hahn_series {f : polynomial K} (hf :f ≠ 0) :
-- --   multiplicity power_series.X (↑f : power_series K) = multiplicity polynomial.X f :=
-- -- begin
-- --   sorry,
-- -- end

-- -- lemma multiplicity_hahn_series_eq_multiplicity_pow_series {φ : hahn_series ℕ K} (hφ : φ ≠ 0) :
-- --   multiplicity (single 1 1) φ = multiplicity power_series.X (to_power_series φ) :=
-- -- begin
-- --   sorry,
-- -- end

instance discrete_fae : uniform_space K := ⊤
section ratfunc_coeff

lemma discrete_complete_fae (d : ℤ) {uK : uniform_space K}
  (h : uniformity K = 𝓟 id_rel) : is_complete (⊤ : (set K)) :=
begin
  sorry
end

def eval_compl_fae (d : ℤ) {uK : uniform_space K}
  (h : uniformity K = 𝓟 id_rel) : (completion_of_ratfunc K) → K := 
  uniform_space.completion.extension (eval_fae K d)

the `instance : uniform_space (completion_of_ratfunc K) :=` is needed for the `lemma` below
lemma cauchy_fae (d : ℤ) {uK : uniform_space K} (h : uniformity K = 𝓟 id_rel)
  (α : filter (ratfunc K)) (hα : cauchy α) :
  cauchy (α.map (ratfunc.coeff_map K d)) := hα.map (unif_cnts_fae K d h)

lemma constant_cauchy_fae_principal {uK : uniform_space K} 
  (h : uniformity K = 𝓟 id_rel) (α : filter K) (hα : cauchy α) :
  α ≤ filter.principal {constant_cauchy_fae K h α hα} := sorry

-/