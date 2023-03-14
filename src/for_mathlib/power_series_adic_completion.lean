/-
Copyright (c) 2022 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import algebra.order.hom.monoid
-- import algebra.hom.group
import for_mathlib.num_denom_away
import for_mathlib.polynomial
import ring_theory.dedekind_domain.adic_valuation
import ring_theory.laurent_series
import ring_theory.power_series.well_known


open polynomial is_dedekind_domain.height_one_spectrum topological_space ratfunc sequentially_complete filter
open_locale big_operators discrete_valuation uniformity filter topology

variables (K : Type*) [field K]

noncomputable theory
def completion_of_ratfunc  := adic_completion (ratfunc K) (ideal_X K)

instance : field (completion_of_ratfunc K) := adic_completion.field (ratfunc K) (ideal_X K)

instance : algebra K (polynomial K) := infer_instance

instance : valued (ratfunc K) ℤₘ₀ := 
begin
 use @adic_valued (polynomial K) _ _ _ (ratfunc K) _ _ _ (ideal_X K),
end

-- instance : uniform_space (ratfunc K) :=
--   (@adic_valued (polynomial K) _ _ _ (ratfunc K) _ _ _ (ideal_X K)).to_uniform_space



-- example : valued (ratfunc K) ℤₘ₀ :=
-- begin
--   have := adic_valued (ideal_X K),
-- end
  -- (@adic_valued (polynomial K) _ _ _ (ratfunc K) _ _ _ (ideal_X K)).to_uniform_space

instance already : valued (completion_of_ratfunc K) ℤₘ₀ :=
  @valued.valued_completion _ _ _ _ (ideal_X K).adic_valued

-- #exit

instance : uniform_space (completion_of_ratfunc K) := infer_instance


variable (F : completion_of_ratfunc K)

--*FAE* The one below is one I am trying on Mar14th at night
def entourage (d : ℤ) : set (ratfunc K × ratfunc K) :=
  {P | (ideal_X K).valuation (P.1 - P.2) < ↑(multiplicative.of_add d)}

--*FAE* The one below is the one that works perfectly but gives something crazy
def entourage' (d : ℤ) : set (ratfunc K × ratfunc K) :=
  {P | (ideal_X K).valuation (P.1 - P.2) < ↑(multiplicative.of_add (- d))}

-- *FAE* This was the old definition, but I think I got the inequalities wrong, since I did not
-- know yet how to play with `multiplicative.of_add`. It does not work
def entourage_bad (d : ℤ) : set (ratfunc K × ratfunc K) :=
  {P | ↑(multiplicative.of_add d) ≤ (ideal_X K).valuation (P.1 - P.2)}

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


-- example (X Y : Type) [preorder X] [has_lt X] (S : set X) (hS : S.is_wf)

-- lemma uno {X Y : Type} [preorder X] [preorder Y] {S : set X} (hS : S.is_pwo)
--   (f : X ↪o Y) : set.is_wf (f '' S) :=
-- begin
--   apply set.is_pwo.is_wf,
--   apply set.is_pwo.image_of_monotone hS f.monotone,
-- end

-- lemma due {X Y : Type} [preorder X] [preorder Y] {S : set X} (hS : S.is_pwo) (H : S.nonempty)
--   (f : X ↪o Y) : f (set.is_wf.min (hS.is_wf) H) = 
--     set.is_wf.min (uno hS f) (set.nonempty_image_iff.2 H) := 
-- begin
--   sorry,
-- end


-- namespace function

-- variables {Γ Γ' : Type} [linear_ordered_cancel_add_comm_monoid Γ] 
--   [linear_ordered_cancel_add_comm_monoid Γ'] {ι : Γ →+o Γ'}

-- @[simps]
-- def injective.order_embedding (hι : function.injective ι) : Γ ↪o Γ' := 
--   order_embedding.of_strict_mono _ ((order_hom_class.mono ι).strict_mono_of_injective hι)

-- end function

-- lemma order_emb_domain {R Γ Γ' : Type} [comm_ring R] [is_domain R]
-- [linear_ordered_cancel_add_comm_monoid Γ]
-- [linear_ordered_cancel_add_comm_monoid Γ'] 
-- (ι : Γ →+o Γ') (hι : function.injective ι) (φ : hahn_series Γ R) :
--   (with_top.map (↑ι : _ →+ _)) (hahn_series.add_val Γ R φ) = hahn_series.add_val Γ' R
--   (emb_domain hι.order_embedding φ) :=
-- begin
--   sorry,
-- end

namespace hahn_series
open set
variables {Γ Γ' R : Type*}  


lemma eq_order_of_emb_domain [has_zero R] [linear_order Γ] [linear_order Γ'] [has_zero Γ] [has_zero Γ'] (φ : hahn_series Γ R) {ι : Γ ↪o Γ'}  (hι : ι 0 = 0) :
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

lemma order_eq_of_power_series_Z {R : Type*} [semiring R] {φ : power_series R} (hφ : φ ≠ 0) :
  ((φ.order).get (power_series.order_finite_iff_ne_zero.mpr hφ) : ℤ) =
    (hahn_series.of_power_series ℤ R φ).order :=
begin
  let ι : ℕ ↪o ℤ := ⟨⟨(nat.cast_add_monoid_hom ℤ).1, nat.strict_mono_cast.injective⟩, λ _ _, nat.cast_le⟩,
  have := @hahn_series.eq_order_of_emb_domain ℕ ℤ R _ _ _ _ _ (of_power_series ℕ R φ) ι nat.cast_zero,
  have pufpuf : emb_domain ι (of_power_series ℕ R φ) = of_power_series ℤ R φ, sorry,
  -- { simp,

  -- },
  rw pufpuf at this,
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

lemma fae_pol_ps_order_mul {f : polynomial K} : --(hf : f ≠ 0) :
  (↑f : power_series K).order = multiplicity polynomial.X f :=
begin
-- sorry,
-- {
  by_cases hf_pol : f = 0, sorry,
  rw power_series.order_eq_multiplicity_X,
  have hf_ps : finite (power_series.X : power_series K) ↑f, sorry,
  set d_ps := (multiplicity power_series.X ↑f).get hf_ps with hd_ps,
  replace hf_pol: finite polynomial.X f, sorry,
  set d_pol := (multiplicity polynomial.X f).get hf_pol with hd_pol,
  obtain ⟨P, hfP, h_nXP⟩ := exists_eq_pow_mul_and_not_dvd hf_pol,
  rw ← hd_pol at hfP,
  obtain ⟨φ, hfφ, h_nXφ⟩ := exists_eq_pow_mul_and_not_dvd hf_ps,
  rw ← hd_ps at hfφ,
  apply le_antisymm,
  { have Hpol := @pow_dvd_iff_le_multiplicity (polynomial K) _ _ X f d_ps,
    rw [X_pow_dvd_pol_iff_dvd_power_series] at Hpol,
    replace Hpol := Hpol.mp (dvd_of_mul_right_eq _ hfφ.symm),
    rwa [hd_ps, part_enat.coe_get] at Hpol,
  },
  have Hps := @pow_dvd_iff_le_multiplicity (power_series K) _ _ power_series.X f,
  sorry,
--   }
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

-- variable {K}
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
-- lemma fae_pol_ps_order_val {f : polynomial K} (hf : f ≠ 0) :
--  ↑(multiplicative.of_add (- (power_series.nat_order (polynomial.coe_ne_zero hf )) : ℤ)) = 
--     ((ideal_X K).int_valuation f) :=
-- begin 
--   have := fae_pol_ps_order_mul,
--   have := power_series.nat_order_eq_order (polynomial.coe_ne_zero hf),
--   sorry,
-- end


--open unique_factorization_monoid
lemma count_normalized_factors_eq_count_normalized_factors_span {R : Type*} [comm_ring R]
  [is_domain R] [is_principal_ideal_ring R] [normalization_monoid R][unique_factorization_monoid R] 
    {r X : R} (hr : r ≠ 0) (hX₀ : X ≠ 0) (hX₁ : norm_unit X = 1 )(hX : prime X) : 
  multiset.count X (unique_factorization_monoid.normalized_factors r) = 
  multiset.count (ideal.span {X} : ideal R ) 
    (unique_factorization_monoid.normalized_factors (ideal.span {r})) :=
begin
  replace hX₁ : X = normalize X, 
  { simp only [normalize_apply, hX₁, units.coe_one, mul_one] },
  have : (ideal.span {normalize X} : ideal  R) = normalize (ideal.span {X}),
  { simp only [normalize_apply, normalize_eq],
    apply ideal.span_singleton_mul_right_unit (units.is_unit _) },
  rw [← part_enat.coe_inj, hX₁,
    ← unique_factorization_monoid.multiplicity_eq_count_normalized_factors hX.irreducible hr, this, 
    ← multiplicity_eq_multiplicity_span, 
    ← unique_factorization_monoid.multiplicity_eq_count_normalized_factors],
  refine prime.irreducible (ideal.prime_of_is_prime _ _),
  {rwa [ne.def, ideal.span_singleton_eq_bot] },
  {rwa ideal.span_singleton_prime hX₀ },
  {rwa [ne.def, ideal.zero_eq_bot, ideal.span_singleton_eq_bot] },
end

--GOLF IT!
lemma count_normalized_factors_eq_associates_count {I J : ideal (polynomial K)} (hI : I ≠ 0) (hJ : J.is_prime ) (hJ₀ : J ≠ ⊥) : multiset.count J (unique_factorization_monoid.normalized_factors I) = 
  (associates.mk J).count (associates.mk I).factors :=
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

lemma order_as_power_series_eq_int_valuation {f : polynomial K} (hf : f ≠ 0) :
  ↑(multiplicative.of_add 
  (-((↑f : power_series K).order).get (power_series.order_finite_iff_ne_zero.mpr
    (polynomial.coe_ne_zero hf)) : ℤ)) = ((ideal_X K).int_valuation f) :=
begin
  rw [fae_pol_ps_nat_order_mul, fae_int_valuation_apply, int_valuation_def_if_neg _ hf],
  simp only [of_add_neg, ideal_X_span, inv_inj, with_zero.coe_inj, embedding_like.apply_eq_iff_eq,
    nat.cast_inj],
  simp_rw [@unique_factorization_monoid.multiplicity_eq_count_normalized_factors (polynomial K)
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
  simpa only [of_add_neg, of_power_series_apply, inv_inj, with_zero.coe_inj, embedding_like.apply_eq_iff_eq, nat.cast_inj],
end


lemma order_as_hahn_series_eq_int_valuation {f : polynomial K} (hf : f ≠ 0) :
 ↑(multiplicative.of_add (- (f : laurent_series K).order)) = ((ideal_X K).int_valuation f) :=
begin
  simp only [← order_as_nat_hahn_series_eq_int_valuation K hf, coe_coe, of_add_neg, inv_inj, with_zero.coe_inj, embedding_like.apply_eq_iff_eq],
  convert (hahn_series.order_eq_of_power_series_Z (polynomial.coe_ne_zero hf)).symm,
  exact (hahn_series.nat_order_eq_of_power_series (polynomial.coe_ne_zero hf)).symm,
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
  replace hfPQ : is_localization.mk' (ratfunc K) P ⟨Q, hQ⟩ = f := by simp only [hfPQ, is_fraction_ring.mk'_eq_div, set_like.coe_mk],
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
  replace hQ₀ : (↑Q : ratfunc K) ≠ 0, sorry,--already done for `P` on the last `{---}` block of the proof below
  apply congr_arg,
  rw neg_eq_iff_neg_eq,
  rw neg_sub_neg,
  rw neg_sub,
  rw ← fae_order_div,
  rw ← hfPQ,
  apply congr_arg,
  convert_to ((↑P : ratfunc K) : laurent_series K)/ (↑Q : ratfunc K) =
    ↑(is_localization.mk' (ratfunc K) P ⟨Q, hQ⟩),
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
    have := ((@injective_iff_map_eq_zero' _ _ _ _ _ _ (_ : (polynomial K) →+* (laurent_series K))).mp hinj P).mp hneP,
    exact hP this,
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
  rw eq_inv_iff_eq_inv,
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

end ratfunc

lemma entourage_uniformity_mem (d : ℤ) : entourage K d ∈ 𝓤 (ratfunc K) :=
begin
  simp only [entourage, of_add_neg, with_zero.coe_inv, mem_comap, exists_prop],
  let T : set (ratfunc K) := {P | ((ideal_X K).valuation) P < (multiplicative.of_add d)⁻¹},
  use {P | ((ideal_X K).valuation) P < (multiplicative.of_add d)⁻¹},
  split,
  { apply (@valued.mem_nhds_zero (ratfunc K) _ ℤₘ₀ _ _ T).mpr,
    use ⟨↑(multiplicative.of_add d)⁻¹, ↑(multiplicative.of_add d), by {simp only [with_zero.coe_inv,
      inv_mul_cancel, ne.def, with_zero.coe_ne_zero, not_false_iff]}, by {simp only
      [with_zero.coe_inv, _root_.mul_inv_cancel, ne.def, with_zero.coe_ne_zero, not_false_iff]}⟩,
    simp only [units.coe_mk, with_zero.coe_inv, set.set_of_subset_set_of],
    exact λ _ ha, ha,
  },
  { simp only [set.preimage_set_of_eq, set.set_of_subset_set_of, prod.forall],
    intros _ _ h,
    rw [← valuation.map_neg, neg_sub],
    
    apply lt_trans h,
    rw ← with_zero.coe_inv,
    rw with_zero.coe_lt_coe,
    rw ← of_add_neg,
    rw multiplicative.of_add_lt,
    sorry,----PENSIAMOCI SU!
    
    
    },
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

lemma bounded_supp_of_mem_entourage (x : ratfunc K) (d : ℤ) : ∃ N : ℤ, ∀ y : ratfunc K, 
  (x, y) ∈ (entourage K d) → ∀ n < N, y.coeff n = 0 :=
begin
  by_cases hx : x = 0,
  { use d,
    intros _ hy _ hn,
    rw [← eq_coeff_of_mem_entourage hy (le_of_lt hn), hx, ratfunc.coeff_zero] },
  { replace hx := ratfunc.coe_ne_zero_iff.mp hx,
    use min ((x : laurent_series K).2.is_wf.min (hahn_series.support_nonempty_iff.mpr hx)) d,
    intros _ hy _ hn,
    have hn' : x.coeff n = 0 := function.nmem_support.mp ( λ h, set.is_wf.not_lt_min
      (x : laurent_series K).2.is_wf (support_nonempty_iff.mpr hx) h (lt_min_iff.mp hn).1),
    rwa ← eq_coeff_of_mem_entourage hy (le_of_lt (lt_min_iff.mp hn).2) },
end

lemma bounded_supp_of_mem_entourage' (x : ratfunc K) (d : ℤ) : ∀ᶠ n in at_bot, ∀ y : ratfunc K, 
  (x, y) ∈ (entourage K d) → y.coeff n = 0 :=
begin
  obtain ⟨N, hN⟩ := bounded_supp_of_mem_entourage x d,
  apply eventually_at_bot.mpr ⟨N - 1, _⟩,
  intros n hn y hy,
  exact hN y hy n (int.lt_of_le_sub_one hn),
end

lemma uniform_continuous_coeff_map {uK : uniform_space K} (h : uniformity K = 𝓟 id_rel) (d : ℤ)
: uniform_continuous (ratfunc.coeff_map K d) :=
begin
  refine uniform_continuous_iff_eventually.mpr _,
  intros S hS,
  rw h at hS,
  refine eventually_iff_exists_mem.mpr ⟨entourage K d, ⟨entourage_uniformity_mem K d, λ x hx, hS _⟩⟩,
  exact eq_coeff_of_mem_entourage hx (le_of_eq (refl _)),
end

namespace set

lemma prod_subset_diag_singleton_left {X : Type*} [nonempty X] {S T : set X} (hS : S.nonempty) (hT : T.nonempty) 
  (h_diag : S ×ˢ T ⊆ id_rel) : ∃ x, S = {x} :=
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
--this `def` has nothing to do with (local) fields
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


lemma cauchy_discrete_converges  {X : Type*} [nonempty X] {uX : uniform_space X} 
  (hX : uniformity X = 𝓟 id_rel) {α : filter X} (hα : cauchy α) : 
  α ≤ 𝓟 {cauchy_discrete_is_constant hX hα} := Exists.some_spec (cauchy_discrete_le_principal hX hα)


lemma eventually_constant {uK : uniform_space K} (h : uniformity K = 𝓟 id_rel)
  {ℱ : filter (ratfunc K)} (hℱ : cauchy ℱ) (n : ℤ) :
  ∀ᶠ x in ℱ, ratfunc.coeff x n = cauchy_discrete_is_constant h 
    (hℱ.map (uniform_continuous_coeff_map h n)) := 
begin
  cases hℱ with ℱ_ne_bot ℱ_le,
  rw [filter.le_def] at ℱ_le,
  specialize ℱ_le _ (entourage_uniformity_mem K n),
  obtain ⟨S, ⟨hS, ⟨T, ⟨hT, H⟩⟩⟩⟩ := filter.mem_prod_iff.mp ℱ_le,
  have S_nempty : S.nonempty, sorry,
  have T_nempty : T.nonempty, sorry,
  rcases ⟨S_nempty, T_nempty⟩ with ⟨⟨s, hs⟩, ⟨t, ht⟩⟩, 
  have H_st : (s,t) ∈ entourage K n, sorry,
  have due := eq_coeff_of_mem_entourage' H_st,
  rw filter.eventually,
end

lemma coeff_entually_zero {uK : uniform_space K} (h : uniformity K = 𝓟 id_rel)
  {ℱ : filter (ratfunc K)} (hℱ : cauchy ℱ) (d : ℤ) :
  ∀ᶠ x in ℱ, ∀ᶠ d in (at_bot : filter ℤ), ratfunc.coeff x d = (0 : K) :=
begin
  sorry
end
  
  -- ratfunc.coeff x d = cauchy_discrete_is_constant h 
  --   (hℱ.map (uniform_continuous_coeff_map K h d)) := 

def isom 
  {uK : uniform_space K} (h : uniformity K = 𝓟 id_rel) : 
  -- adic_completion.field (ratfunc K) (ideal_X K) ≃ ℤ := sorry
  (completion_of_ratfunc K) ≃ (laurent_series K) :=
{ to_fun :=
  begin
  intro α,
  apply hahn_series.mk,
  swap,
  intro d,
  obtain ⟨ℱ, hℱ⟩ := (quot.exists_rep α).some,
  use (cauchy_discrete_is_constant h --(ℱ.map (ratfunc.coeff_map K d))
    (hℱ.map (uniform_continuous_coeff_map h d))),
  sorry,
  -- have : set.is_pwo (⊤ : (set ℤ)),
  -- apply set.is_wf.is_pwo,
  -- apply set.is_wf_univ_iff.mpr,
  -- refine well_founded.well_founded_iff_has_min.mpr _,


  -- exact set.is_pwo.mono this (set.subset_univ _),
  end,
  inv_fun := sorry,
  left_inv := sorry,
  right_inv := sorry }

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