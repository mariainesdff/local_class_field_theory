/-
Copyright (c) 2023 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import algebra.group.with_one.units
import discrete_valuation_ring.basic
import for_mathlib.stuff_for_laurent_series 
import from_mathlib.PR18604_well_founded
import topology.uniform_space.abstract_completion
import for_mathlib.with_zero

noncomputable theory

open abstract_completion is_dedekind_domain.height_one_spectrum polynomial power_series
   uniform_space 
open_locale discrete_valuation

namespace completion_laurent_series

open_locale classical

variables (K : Type*) [field K]

def power_series.ideal_X (K : Type*) [field K] : is_dedekind_domain.height_one_spectrum 
  (power_series K) := 
  { as_ideal := ideal.span({X}),
  is_prime := power_series.span_X_is_prime,
  ne_bot   := by { rw [ne.def, ideal.span_singleton_eq_bot], exact X_ne_zero }} 


open multiplicity principal_ideal_ring unique_factorization_monoid

lemma polynomial.norm_unit_X : norm_unit (polynomial.X : (polynomial K)) = 1 :=
begin
  have := @coe_norm_unit K _ _ _ polynomial.X,
  rwa [leading_coeff_X, norm_unit_one, units.coe_one, map_one, units.coe_eq_one] at this,
end

lemma polynomial.X_eq_normalize : (polynomial.X : (polynomial K)) = normalize polynomial.X :=
by simp only [normalize_apply, polynomial.norm_unit_X, units.coe_one, mul_one]

lemma power_series.norm_unit_X : norm_unit (power_series.X : (power_series K)) = 1 :=
by {dsimp only [norm_unit],rw [inv_eq_one, ← units.coe_eq_one, unit_of_divided_by_X_pow_nonzero,
    divided_by_X_pow_of_X_eq_one]}

lemma power_series.X_eq_normalize : 
  (power_series.X : (power_series K)) = normalize power_series.X :=
by simp only [normalize_apply, power_series.norm_unit_X, units.coe_one, mul_one]

lemma factors_in_pol_eq_power_series (P : (polynomial K)) (hP : P ≠ 0) : 
  (normalized_factors (ideal.span {↑P})).count (power_series.ideal_X K).as_ideal =
  (normalized_factors (ideal.span {P})).count (ideal.span {polynomial.X} : ideal (polynomial K)) :=
begin
  have for_pol := principal_ideal_ring.count_normalized_factors_eq_count_normalized_factors_span hP
    polynomial.X_ne_zero (polynomial.norm_unit_X K) polynomial.prime_X,
  rw [← for_pol],
  have for_pow := principal_ideal_ring.count_normalized_factors_eq_count_normalized_factors_span
    (coe_ne_zero hP) power_series.X_ne_zero (power_series.norm_unit_X K) power_series.X_prime,
  erw [← for_pow],
  have aux_pol := @multiplicity_eq_count_normalized_factors (polynomial K) _ _ _ _ _ _ 
    polynomial.X P (irreducible_X) hP,
  have aux_pow_series := @multiplicity_eq_count_normalized_factors (power_series K) _ _ _ _ _ _
    power_series.X ↑P (prime.irreducible power_series.X_prime) (coe_ne_zero hP),
  apply nat.le_antisymm,
  { rw [polynomial.X_eq_normalize, power_series.X_eq_normalize, ← part_enat.coe_le_coe, ← aux_pol, 
      ← multiplicity.pow_dvd_iff_le_multiplicity, polynomial.X_pow_dvd_iff],
    intros d hd,
    replace aux_pow_series := le_of_eq aux_pow_series.symm,
    rw [← multiplicity.pow_dvd_iff_le_multiplicity, power_series.X_pow_dvd_iff] at aux_pow_series,
    replace aux_pow_series := aux_pow_series d hd,
    rwa [polynomial.coeff_coe P d] at aux_pow_series },
  { rw [polynomial.X_eq_normalize, power_series.X_eq_normalize, ← part_enat.coe_le_coe,
      ← aux_pow_series, ← multiplicity.pow_dvd_iff_le_multiplicity, power_series.X_pow_dvd_iff],
    intros d hd,
    replace aux_pol := le_of_eq aux_pol.symm,
    rw [← multiplicity.pow_dvd_iff_le_multiplicity, polynomial.X_pow_dvd_iff] at aux_pol,
    replace aux_pol := aux_pol d hd,
    rwa [← polynomial.coeff_coe P d] at aux_pol },
end

lemma pol_int_valuation_eq_power_series (P : (polynomial K)) : (ideal_X K).int_valuation (P) =
  (power_series.ideal_X K).int_valuation (↑P : (power_series K)) :=
begin
  by_cases hP : P = 0,
  { rw [hP, valuation.map_zero, polynomial.coe_zero, valuation.map_zero] },
  { simp only [int_valuation_apply],
    rw [int_valuation_def_if_neg _ hP, int_valuation_def_if_neg _ $ coe_ne_zero hP],
    simp only [ideal_X_span, of_add_neg, inv_inj, with_zero.coe_inj, embedding_like.apply_eq_iff_eq,
      nat.cast_inj],
    have span_ne_zero : (ideal.span {P} : ideal (polynomial K)) ≠ 0 ∧
    (ideal.span {polynomial.X} : ideal (polynomial K)) ≠ 0 := by simp only [ideal.zero_eq_bot,
    ne.def, ideal.span_singleton_eq_bot, hP, polynomial.X_ne_zero, not_false_iff, and_self],
    have span_X_prime : (ideal.span {polynomial.X} : ideal (polynomial K)).is_prime,
    { apply (@ideal.span_singleton_prime (polynomial K) _ _ polynomial.X_ne_zero).mpr prime_X },
    have := count_normalized_factors_eq_associates_count (polynomial K) (ideal.span {P})
    (ideal.span {polynomial.X}) span_ne_zero.1 ((@ideal.span_singleton_prime (polynomial K) _ _ 
    polynomial.X_ne_zero).mpr prime_X) span_ne_zero.2,
    convert this.symm,
    have span_ne_zero' : (ideal.span {↑P} : ideal (power_series K)) ≠ 0 ∧
    ((power_series.ideal_X K).as_ideal : ideal (power_series K)) ≠ 0 := by simp only [ne.def, 
      ideal.zero_eq_bot, ideal.span_singleton_eq_bot, coe_ne_zero hP, power_series.X_ne_zero,
      not_false_iff, and_self, (power_series.ideal_X K).3],
    rw [← factors_in_pol_eq_power_series _ _ hP],
    convert (count_normalized_factors_eq_associates_count (power_series K) (ideal.span {↑P})
    (power_series.ideal_X K).as_ideal span_ne_zero'.1 (power_series.ideal_X K).2
      span_ne_zero'.2).symm }
end

instance : valued (laurent_series K) ℤₘ₀ := valued.mk' (power_series.ideal_X K).valuation

section complete

open filter topological_space laurent_series
open_locale filter topology uniformity

lemma coeff_zero_of_lt_int_valuation {n d : ℕ} {f : power_series K}
  (H : valued.v (f : laurent_series K) ≤
    ↑(multiplicative.of_add ((- d) : ℤ))) : n < d → coeff K n f = 0 :=
begin
  intro hnd,
  convert (@power_series.X_pow_dvd_iff K _ d f).mp _ n hnd,
  have := @valuation_of_algebra_map (power_series K) _ _ _ (laurent_series K) _ _ _
    (power_series.ideal_X K) f,--togliere `@`
  erw this at H,
  have dvd_val_int := (@int_valuation_le_pow_iff_dvd (power_series K) _ _ _ (power_series.ideal_X K)
    f d).mp H,
  rw [← span_singleton_dvd_span_singleton_iff_dvd, ← ideal.span_singleton_pow],
  apply dvd_val_int,
end

lemma int_valuation_le_iff_coeff_zero_of_lt {d : ℕ} (f : power_series K) :
valued.v (f : laurent_series K) ≤ ↑(multiplicative.of_add ((- d) : ℤ))
   ↔ (∀ n : ℕ, n < d → coeff K n f = 0) :=
begin
  have : power_series.X ^ d ∣ f ↔ ∀ n : ℕ, n < d → (coeff K n) f = 0,
  exact ⟨λ hd n hnd, power_series.X_pow_dvd_iff.mp hd n hnd, λ H, power_series.X_pow_dvd_iff.mpr H⟩,
  erw [← this, valuation_of_algebra_map (power_series.ideal_X K) f, 
    ← span_singleton_dvd_span_singleton_iff_dvd, ← ideal.span_singleton_pow],
  apply int_valuation_le_pow_iff_dvd,
end

lemma int_valuation_of_X : ((power_series.ideal_X K).int_valuation) X =
  ↑(multiplicative.of_add (-1 : ℤ)) := 
begin
  rw [int_valuation_apply, int_valuation_def_if_neg (power_series.ideal_X K)
    power_series.X_ne_zero],
  congr,
  apply associates.count_self,
  rw associates.irreducible_mk,
  apply prime.irreducible,
  apply ideal.prime_of_is_prime,
  apply ideal.span_singleton_eq_bot.mp.mt,
  apply power_series.X_ne_zero,
  apply power_series.span_X_is_prime,
end

lemma valuation_of_X_zpow (s : ℕ) :
  valued.v ((↑(power_series.X : (power_series K)) : (laurent_series K)) ^ s) = 
    ↑(multiplicative.of_add (- (s : ℤ))) :=
begin
  have : valued.v (↑(power_series.X : (power_series K))) = 
    (↑(multiplicative.of_add (- (1 : ℤ))) : ℤₘ₀),
  { erw @valuation_of_algebra_map (power_series K) _ _ _ (laurent_series K) _ _ _
    (power_series.ideal_X K) (power_series.X),
    apply int_valuation_of_X K },
  rw [map_pow, this, ← one_mul ↑s, ← neg_mul (1 : ℤ) ↑s, int.of_add_mul, with_zero.coe_zpow, 
    of_add_neg, with_zero.coe_inv, zpow_coe_nat],
end

lemma valuation_of_single_zpow (s : ℤ) :
  valued.v ((hahn_series.single s (1 : K)) : (laurent_series K)) = 
    ↑(multiplicative.of_add (- (s : ℤ))) :=
begin
  have aux_mul : (hahn_series.single s (1 : K)) * (hahn_series.single (-s) (1 : K)) =
    (1 : laurent_series K),
  { rw [hahn_series.single_mul_single, ← sub_eq_add_neg, sub_self, one_mul],
    refl },
  have H : (valued.v (1 : laurent_series K)) = (1 : ℤₘ₀) := valued.v.map_one,
  rw [← aux_mul, map_mul, mul_eq_one_iff_eq_inv₀] at H,
  { rw H,
    induction s with s s,
    { rw [int.of_nat_eq_coe, ← hahn_series.of_power_series_X_pow, ← coe_power_series] at H,
      rw [int.of_nat_eq_coe, ← H, power_series.coe_pow, valuation_of_X_zpow] },
    { simp only [int.neg_succ_of_nat_coe, neg_neg, ← hahn_series.of_power_series_X_pow,
      ← coe_power_series, power_series.coe_pow, valuation_of_X_zpow, of_add_neg, with_zero.coe_inv,
        inv_inv] }},
  { rw valuation.ne_zero_iff,
    simp only [ne.def, one_ne_zero, not_false_iff, hahn_series.single_ne_zero]},
end

lemma coeff_zero_of_lt_valuation {n D : ℤ} {f : laurent_series K} 
  (H : valued.v f ≤ ↑(multiplicative.of_add (- D))) : n < D → f.coeff n = 0 :=
begin
  intro hnd,
  by_cases h_n_ord : n < f.order,
  { exact hahn_series.coeff_eq_zero_of_lt_order h_n_ord },
  { rw not_lt at h_n_ord,
    set F := power_series_part f with hF,--not really necessary
    by_cases ord_nonpos : f.order ≤ 0,
    { obtain ⟨s, hs⟩ := int.exists_eq_neg_of_nat ord_nonpos,
      rw [hs] at h_n_ord,
      obtain ⟨m, hm⟩ := int.eq_coe_of_zero_le (neg_le_iff_add_nonneg.mp h_n_ord),
      have hD : 0 ≤  D + s:= by linarith,
      obtain ⟨d, hd⟩ := int.eq_coe_of_zero_le hD,
      have F_coeff := power_series_part_coeff f m,
      rw [hs, add_comm, ← eq_add_neg_of_add_eq hm, ← hF] at F_coeff,
      rw [← F_coeff],
      refine (@int_valuation_le_iff_coeff_zero_of_lt K _ d F).mp _ m (by linarith),
      have F_mul := of_power_series_power_series_part f,
      rw [← hF, hs, neg_neg, ← hahn_series.of_power_series_X_pow s, ← coe_power_series,
        ← coe_power_series] at F_mul,
      rwa [F_mul, map_mul, ← hd, power_series.coe_pow, neg_add_rev, of_add_add, with_zero.coe_mul,
        valuation_of_X_zpow K s, mul_le_mul_left₀],
      simp only [ne.def, with_zero.coe_ne_zero, not_false_iff], },
    { rw not_le at ord_nonpos,
      obtain ⟨s, hs⟩ := int.exists_eq_neg_of_nat (int.neg_nonpos_of_nonneg (le_of_lt ord_nonpos)),
      rw neg_inj at hs,
      rw [hs, ← sub_nonneg] at h_n_ord,
      obtain ⟨m, hm⟩ := int.eq_coe_of_zero_le h_n_ord,
      rw sub_eq_iff_eq_add at hm,
      have hD : 0 ≤  D - s := by linarith,
      obtain ⟨d, hd⟩ := int.eq_coe_of_zero_le hD,
      have F_coeff := power_series_part_coeff f m,
      rw [hs, add_comm, ← hF, ← hm] at F_coeff,
      rw ← F_coeff,
      refine (@int_valuation_le_iff_coeff_zero_of_lt K _ d F).mp _ m (by linarith),
      have F_mul := of_power_series_power_series_part f,
      rw [← hF, ← coe_power_series] at F_mul,
      rwa [F_mul, map_mul, ← hd, hs, neg_sub, sub_eq_add_neg, of_add_add, valuation_of_single_zpow, 
        neg_neg, with_zero.coe_mul, mul_le_mul_left₀],
      simp only [ne.def, with_zero.coe_ne_zero, not_false_iff] }}
end

lemma valuation_le_iff_coeff_zero_of_lt {D : ℤ} {f : laurent_series K} :
  valued.v f ≤ ↑(multiplicative.of_add ((- D) : ℤ)) ↔ (∀ n : ℤ, n < D → f.coeff n = 0) :=
begin
  refine ⟨λ hnD n hn, coeff_zero_of_lt_valuation K hnD hn, λ h_val_f, _⟩,
  set F := power_series_part f with hF, --not really necessary
  by_cases ord_nonpos : f.order ≤ 0,
  { obtain ⟨s, hs⟩ := int.exists_eq_neg_of_nat ord_nonpos,
    have h_F_mul := f.single_order_mul_power_series_part,
    rw [hs, ← hF] at h_F_mul,
    rw [← h_F_mul, map_mul, valuation_of_single_zpow, neg_neg, mul_comm, ← le_mul_inv_iff₀,
      of_add_neg, with_zero.coe_inv, ← mul_inv, ← with_zero.coe_mul, ← of_add_add, 
      ← with_zero.coe_inv, ← of_add_neg],
      by_cases hDs : D + s ≤ 0,
      { apply le_trans ((power_series.ideal_X K).valuation_le_one F),
        rwa [← with_zero.coe_one, ← of_add_zero, with_zero.coe_le_coe, multiplicative.of_add_le,
          left.nonneg_neg_iff] },
      { rw not_le at hDs,
        obtain ⟨d, hd⟩ := int.eq_coe_of_zero_le (le_of_lt hDs),
        rw hd,
        apply (int_valuation_le_iff_coeff_zero_of_lt K F).mpr,
        intros n hn,
        rw [power_series_part_coeff f n, hs],
        apply h_val_f,
        linarith },
      simp only [ne.def, with_zero.coe_ne_zero, not_false_iff] },
    { rw not_le at ord_nonpos,
      obtain ⟨s, hs⟩ := int.exists_eq_neg_of_nat (int.neg_nonpos_of_nonneg (le_of_lt ord_nonpos)),
      rw neg_inj at hs,
      have h_F_mul := f.single_order_mul_power_series_part,
      rw [hs, ← hF] at h_F_mul,
      rw [← h_F_mul, map_mul, valuation_of_single_zpow, mul_comm, ← le_mul_inv_iff₀, of_add_neg,
        with_zero.coe_inv, ← mul_inv, ← with_zero.coe_mul, ← of_add_add, ← with_zero.coe_inv, 
        ← of_add_neg, neg_add, neg_neg], 
      by_cases hDs : D - s ≤ 0,
      { apply le_trans ((power_series.ideal_X K).valuation_le_one F),
        rw [← with_zero.coe_one, ← of_add_zero, with_zero.coe_le_coe, multiplicative.of_add_le],
        linarith},
      { rw not_le at hDs,
        obtain ⟨d, hd⟩ := int.eq_coe_of_zero_le (le_of_lt hDs),
        rw [← neg_neg (-D + ↑s)],
        rw ← sub_eq_neg_add,
        rw neg_sub,
        rw hd,
        apply (int_valuation_le_iff_coeff_zero_of_lt K F).mpr,
        intros n hn,
        rw [power_series_part_coeff f n, hs],
        apply h_val_f (s + n),
        linarith },
      simp only [ne.def, with_zero.coe_ne_zero, not_false_iff] },
end

lemma valuation_le_of_coeff_eventually_eq {f g : (laurent_series K)} {D : ℤ}
  (H : ∀ d, d < D → g.coeff d = f.coeff d) : valued.v (f - g) ≤ ↑(multiplicative.of_add (- D)) :=
begin
  apply (valuation_le_iff_coeff_zero_of_lt K).mpr,
  intros n hn,
  rw [hahn_series.sub_coeff, sub_eq_zero],
  exact (H n hn).symm,
end

lemma eq_coeff_of_valuation_sub_lt {d n : ℤ} {f g : laurent_series K} 
  (H : valued.v (g - f) ≤ ↑(multiplicative.of_add (- d))) :
  n < d → g.coeff n = f.coeff n :=
begin
  by_cases triv : g = f,
  { exact (λ _, by rw triv) },
  { intro hn,
    apply eq_of_sub_eq_zero,
    erw [← hahn_series.sub_coeff],
    apply coeff_zero_of_lt_valuation K H hn }
end


lemma uniform_continuous_coeff {uK : uniform_space K} (h : uniformity K = 𝓟 id_rel) (d : ℤ) :
  uniform_continuous (λ (f : laurent_series K), f.coeff d) :=
begin
  refine uniform_continuous_iff_eventually.mpr (λ S hS, eventually_iff_exists_mem.mpr _),
  let γ : ℤₘ₀ˣ := units.mk0 (↑(multiplicative.of_add (- (d + 1)))) with_zero.coe_ne_zero,
  use {P | valued.v (P.snd - P.fst) < ↑γ},
  refine  ⟨(valued.has_basis_uniformity (laurent_series K) ℤₘ₀).mem_of_mem (by tauto), λ P hP, _⟩,
  rw [h] at hS,
  apply hS,
  rw [eq_coeff_of_valuation_sub_lt K (le_of_lt hP) (lt_add_one _), mem_id_rel],
end

/- The definition below avoids the assumption that `K` be endowed with the trivial uniformity,
  rather putting this in the proof.
-/
variable {K}
def cauchy.coeff {ℱ : filter (laurent_series K)} (hℱ : cauchy ℱ) : ℤ → K :=
begin
  letI : uniform_space K := ⊥,
  have hK : @uniformity K ⊥ = filter.principal id_rel := rfl,
  use λ d, cauchy_discrete_is_constant hK (hℱ.map (uniform_continuous_coeff K hK d)),
end

lemma aux_coeff_map {ℱ : filter (laurent_series K)} (hℱ : cauchy ℱ) (D : ℤ) : 
  tendsto (λ (f : laurent_series K), f.coeff D) ℱ (𝓟 {cauchy.coeff hℱ D}) :=
begin
  letI : uniform_space K := ⊥,
  have hK : uniformity K = filter.principal id_rel, refl,
  exact cauchy_discrete_le hK (hℱ.map (uniform_continuous_coeff K hK D)),
end

lemma bounded_supp_of_valuation_le (f : laurent_series K) (d : ℤ) : ∃ N : ℤ,
∀ (g : laurent_series K), valued.v (g - f) ≤ ↑(multiplicative.of_add (- d)) →
  ∀ n < N, g.coeff n = 0 :=
begin
  by_cases hf : f = 0,
  { refine ⟨d, λ _ hg _ hn, _⟩,
    simpa only [eq_coeff_of_valuation_sub_lt K hg hn, hf] using hahn_series.zero_coeff },
  { refine ⟨min (f.2.is_wf.min (hahn_series.support_nonempty_iff.mpr hf)) d - 1, λ _ hg n hn, _⟩,
    have hn' : f.coeff n = 0 := function.nmem_support.mp ( λ h, set.is_wf.not_lt_min
      f.2.is_wf (hahn_series.support_nonempty_iff.mpr hf) h _),
    rwa eq_coeff_of_valuation_sub_lt K hg _,
    { exact lt_trans hn (int.lt_of_le_sub_one $ (sub_le_sub_iff_right _).mpr (min_le_right _ d)) },
    { exact lt_trans hn (int.lt_of_le_sub_one $ (sub_le_sub_iff_right _).mpr (min_le_left _ _)) }},
end

lemma cauchy.bot₁ {ℱ : filter (laurent_series K)} (hℱ : cauchy ℱ) : ∃ N, 
  ∀ᶠ (f : (laurent_series K)) in ℱ, ∀ n < N, f.coeff n = (0 : K) :=
begin
  let entourage := {P : (laurent_series K) × (laurent_series K) | valued.v (P.snd - P.fst)
    < ↑(multiplicative.of_add (0 : ℤ))},
  let ζ : ℤₘ₀ˣ := units.mk0 (↑(multiplicative.of_add 0)) with_zero.coe_ne_zero,
  obtain ⟨S, ⟨hS, ⟨T, ⟨hT, H⟩⟩⟩⟩ := mem_prod_iff.mp (filter.le_def.mp hℱ.2 entourage
    (@has_basis.mem_of_mem _ _ _ _ _ ζ ((valued.has_basis_uniformity (laurent_series K) ℤₘ₀)) _)),
  obtain ⟨f, hf⟩ := forall_mem_nonempty_iff_ne_bot.mpr hℱ.1 (S ∩ T)
    (by {exact inter_mem_iff.mpr ⟨hS, hT⟩}),
  obtain ⟨N, hN⟩ := bounded_supp_of_valuation_le f 0,
  use N,
  apply mem_of_superset (inter_mem hS hT),
  suffices : (S ∩ T) ×ˢ (S ∩ T) ⊆ entourage,
  { intros g hg,
    have h_prod : (f, g) ∈ entourage,
    { refine this (set.mem_prod.mpr _),
      exact ⟨hf, hg⟩ },
    exact (λ _ hn, hN g (le_of_lt h_prod) _ hn) },
  exacts [(set.prod_mono (set.inter_subset_left S T) (set.inter_subset_right S T)).trans H, trivial]
end

lemma cauchy.bot_aux {ℱ : filter (laurent_series K)} (hℱ : cauchy ℱ) : ∃ N, 
  ∀ n < N, ℱ.map (λ (f : laurent_series K), f.coeff n) ≤ filter.principal {0} :=
begin
  simp only [principal_singleton, pure_zero, nonpos_iff, mem_map],
  obtain ⟨N, hN⟩ := hℱ.bot₁,
  use  N,
  intros n hn,
  apply filter.mem_of_superset hN,
  intros a ha,
  exact ha n hn,
end

lemma cauchy.bot₂ {ℱ : filter (laurent_series K)} (hℱ : cauchy ℱ) : ∃ N, ∀ n,
  n < N → (hℱ.coeff n) = 0 :=
begin
  letI : uniform_space K := ⊥,
  have hK : uniformity K = filter.principal id_rel, refl,
  obtain ⟨N, hN⟩ := hℱ.bot_aux,
  use N,
  intros n hn,
  refine ne_bot_unique_principal hK (hℱ.map (uniform_continuous_coeff K hK n)).1
    (aux_coeff_map _ _) (hN n hn),
end

/-- The following lemma shows that for every `d` smaller than the minimum between the integers
produced in `cauchy.bot₁` and `cauchy.bot₂`, for almost all series in `ℱ` the `d`th coefficient
coincides with the `d`th coefficient of `hℱ.coeff`.
-/
lemma cauchy.bot₃ {ℱ : filter (laurent_series K)} (hℱ : cauchy ℱ) : ∃ N,
  ∀ᶠ (f : laurent_series K) in ℱ, ∀ d < N, (hℱ.coeff d) = f.coeff d :=
begin
  obtain ⟨⟨N₁, hN₁⟩, ⟨N₂, hN₂⟩⟩ := ⟨hℱ.bot₁, hℱ.bot₂⟩,
  refine ⟨min N₁ N₂, ℱ.3 hN₁ (λ _ hf d hd, _)⟩,
  rw [hf d (lt_of_lt_of_le hd (min_le_left _ _)), hN₂ d (lt_of_lt_of_le hd (min_le_right _ _))],
end

lemma cauchy.coeff_support_bdd {ℱ : filter (laurent_series K)} (hℱ : cauchy ℱ) :
  bdd_below (hℱ.coeff.support) :=
begin
  refine ⟨hℱ.bot₂.some, λ d hd, _⟩,
  by_contra' hNd,
  exact hd (hℱ.bot₂.some_spec d hNd),
end

def cauchy.mk_laurent_series {ℱ : filter (laurent_series K)}
  (hℱ : cauchy ℱ) : (laurent_series K) :=
hahn_series.mk (λ d, hℱ.coeff d) (set.is_wf.is_pwo (hℱ.coeff_support_bdd.well_founded_on_lt))


open_locale big_operators


lemma set_inter_Iio {α β: Type*} [linear_order β] {X : β → set α} {D N : β} (hND : N ≤ D) :
  (⋂ d ∈ (set.Iio D), X d) = (⋂ d ∈ (set.Iio N), X d) ∩ (⋂ d ∈ (set.Ico N D), X d) :=
begin
  by_cases hND₀ : N = D,
  { haveI : is_empty {d | D ≤ d ∧ d < D},
    { simp only [set.coe_set_of, is_empty_subtype, not_and, not_lt, imp_self, implies_true_iff] },
    have aux : (⋂ (d : β) (x : D ≤ d ∧ d < D), X d) = set.univ,
    { erw set.bInter_eq_Inter {d | D ≤ d ∧ d < D} (λ x _, X x),
      apply set.Inter_of_empty },
    simp only [hND₀, set.mem_Iio, set.mem_Ico, aux, set.inter_univ] },
  { replace hND := lt_of_le_of_ne hND hND₀,
    rw [← set.Inter_inter_distrib, ← max_eq_right (le_refl D), ← set.Iio_union_Ioo
      (min_lt_of_left_lt hND), max_eq_right (le_refl D)],
    congr' with d,
    simp only [set.mem_union, set.mem_Iio, set.mem_Ico, set.mem_Ioo, set.mem_Inter,
      set.mem_inter_iff, and_imp],
    refine ⟨λ h, ⟨λ H, h $ or.inl $ H.trans hND, λ H h_ND, h $ or.inl h_ND⟩,
      λ h H, _⟩,
    rcases H with Ha | Hb,
    by_cases H_Nd : d < N,
    exacts [h.1 H_Nd, h.2 (le_of_not_lt H_Nd) Ha, h.2 (le_of_lt Hb.1) Hb.2] },
end


lemma cauchy.eventually₁ {ℱ : filter (laurent_series K)} (hℱ : cauchy ℱ) :
  ∀ D : ℤ, ∀ᶠ (f : laurent_series K) in ℱ, ∀ d, d < D → (hℱ.coeff d) = f.coeff d := 
begin
  intro D,
  set X : ℤ → set (laurent_series K) := λ d, {f | (hℱ.coeff d) = f.coeff d} with hX,
  have intersec : (⋂ n ∈ (set.Iio D), X n) ⊆ {x : laurent_series K | ∀ (d : ℤ), d < D 
    → hℱ.coeff d = x.coeff d},
  { rintro (_ hf n hn),
    simp only [set.mem_Inter, set.mem_set_of_eq, hX] at hf,
    exact hf n hn, },
  set N := min hℱ.bot₃.some D with hN₀,
  suffices : (⋂ n ∈ (set.Iio D), X n) ∈ ℱ,
  exact ℱ.3 this intersec,
  by_cases H : D < hℱ.bot₃.some,
  { apply ℱ.3 hℱ.bot₃.some_spec,
    simp only [set.mem_Iio, set.subset_Inter₂_iff, set.set_of_subset_set_of],
    intros m hm f hd,
    exact hd _ (lt_trans hm H)},
  { rw [set_inter_Iio (min_le_right N D), filter.inter_mem_iff, min_eq_left (min_le_right _ _),
    ← hN₀],
    split,
    { rw [hN₀, min_eq_left (not_lt.mp H), hX],
      convert hℱ.bot₃.some_spec,
      ext f,
      simpa only [set.mem_Inter, set.mem_set_of_eq, set.mem_set_of_eq]},
    { have : (⋂ (n : ℤ) (H : n ∈ set.Ico N D), X n) = ⋂ (n : ((finset.Ico N D) : (set ℤ))), X n,
      { simp only [set.mem_Ico, set.Inter_coe_set, finset.mem_coe, finset.mem_Ico, subtype.coe_mk]},
      simp only [this, filter.Inter_mem],
      intro d,
      apply aux_coeff_map hℱ,
      simpa only [principal_singleton, mem_pure] using rfl }}
end


lemma cauchy.eventually₂ {ℱ : filter (laurent_series K)} (hℱ : cauchy ℱ)
  {U : set (laurent_series K)} (hU : U ∈ 𝓝 (hℱ.mk_laurent_series)) : ∀ᶠ f in ℱ, f ∈ U := 
begin
  obtain ⟨γ, hU₁⟩ := valued.mem_nhds.mp hU,
  suffices : ∀ᶠ f in ℱ, f ∈ {y : laurent_series K | valued.v (y - hℱ.mk_laurent_series) < ↑γ},
  { apply this.mono (λ _ hf, hU₁ hf) },
  { set D := -( multiplicative.to_add (with_zero.unzero γ.ne_zero) - 1) with hD₀,
    have hD : ((multiplicative.of_add (-D)) : ℤₘ₀) < γ,
    { rw [← with_zero.coe_unzero γ.ne_zero, with_zero.coe_lt_coe, hD₀, neg_neg, of_add_sub,
        of_add_to_add, div_lt_comm, div_self', ← of_add_zero, multiplicative.of_add_lt],
      exact zero_lt_one, },
    apply (hℱ.eventually₁ D).mono,
    intros f hf,
    apply lt_of_le_of_lt (valuation_le_of_coeff_eventually_eq _ _) hD,
    apply hf }
end

instance : complete_space (laurent_series K) :=
  ⟨λ _ hℱ, ⟨hℱ.mk_laurent_series, λ S hS, hℱ.eventually₂ hS⟩⟩

end complete

section dense 

open laurent_series hahn_series

lemma exists_pol_int_val_lt (F : power_series K) (η : ℤₘ₀ˣ) : ∃ (P : polynomial K),
  (power_series.ideal_X K).int_valuation (F - P) < η :=
begin
  classical,
  by_cases h_neg' : 1 < η,
  { use 0,
    rw [polynomial.coe_zero, sub_zero],
    apply lt_of_le_of_lt (int_valuation_le_one (power_series.ideal_X K) F),
    rwa [← units.coe_one, units.coe_lt_coe] },
  { set D := multiplicative.to_add (with_zero.unzero η.ne_zero) with hD,
    rw [not_lt, ← units.coe_le_coe, units.coe_one, ← with_zero.coe_one,
    ← with_zero.coe_unzero η.ne_zero, with_zero.coe_le_coe, ← multiplicative.to_add_le, ← hD, 
    to_add_one] at h_neg',  
    obtain ⟨d, hd⟩ := int.exists_eq_neg_of_nat h_neg',
    use F.trunc (d+1),
    have trunc_prop : ∀ m : ℕ, m < d + 1 → power_series.coeff K m (F -
      ↑(F.trunc (d+1))) = 0,
    { intros m hm,
      rw [map_sub, sub_eq_zero, polynomial.coeff_coe, coeff_trunc, if_pos hm] },
    have := (int_valuation_le_iff_coeff_zero_of_lt K _).mpr trunc_prop,
    rw [nat.cast_add, neg_add, of_add_add, ← hd, hD, of_add_to_add, with_zero.coe_mul,
      with_zero.coe_unzero, laurent_series.coe_power_series, ← laurent_series.coe_algebra_map]
      at this, 
    rw [← @valuation_of_algebra_map (power_series K) _ _ _ (laurent_series K) _ _ _
      (power_series.ideal_X K) (F - ↑(F.trunc (d+1)))],
    apply lt_of_le_of_lt this,
    rw [← mul_one ↑η, mul_assoc, one_mul],
    apply with_zero.lt_mul_left₀ _ η.ne_zero,
    rw [← with_zero.coe_one, with_zero.coe_lt_coe, algebra_map.coe_one, of_add_neg,
      right.inv_lt_one_iff, ← of_add_zero, multiplicative.of_add_lt],
    apply int.zero_lt_one },
end

lemma exists_ratfunc_val_lt (f : laurent_series K) (γ : ℤₘ₀ˣ) :
  ∃ (Q : ratfunc K), valued.v (f - Q) < γ :=
begin
  set F := f.power_series_part with hF,
  by_cases ord_nonpos : f.order < 0,
  { have h₀ : ((multiplicative.of_add f.order) : ℤₘ₀) ≠ 0 := with_zero.coe_ne_zero,
    set η : ℤₘ₀ˣ := units.mk0 (multiplicative.of_add f.order) h₀ with hη,
    obtain ⟨P, hP⟩ := exists_pol_int_val_lt K F (η * γ),
    use (ratfunc.X)^(f.order) * ↑P,
    have F_mul := f.of_power_series_power_series_part,
    obtain ⟨s, hs⟩ := int.exists_eq_neg_of_nat (le_of_lt ord_nonpos),
    rw [← hF, hs, neg_neg, ← hahn_series.of_power_series_X_pow s, ← laurent_series.coe_power_series,
      ← laurent_series.coe_power_series, ← inv_mul_eq_iff_eq_mul₀] at F_mul,
    erw [hs, ← F_mul, power_series.coe_pow, power_series.coe_X, ratfunc.coe_mul, zpow_neg,
     zpow_coe_nat, inv_eq_one_div (ratfunc.X ^ s), ratfunc.coe_div, ratfunc.coe_pow, ratfunc.coe_X,
     ratfunc.coe_one, ← inv_eq_one_div, ← mul_sub, map_mul, map_inv₀, ← power_series.coe_X,
     valuation_of_X_zpow, ← hs, ← polynomial.coe_coe, ← coe_sub, laurent_series.coe_power_series, 
     ← laurent_series.coe_algebra_map, valuation_of_algebra_map, ← units.coe_mk0 h₀, ← hη],
    apply inv_mul_lt_of_lt_mul₀,
    rwa ← units.coe_mul,
    { simp only [power_series.coe_pow, pow_ne_zero, power_series.coe_X, ne.def,
      hahn_series.single_eq_zero_iff, one_ne_zero, not_false_iff] }},
    { obtain ⟨s, hs⟩ := int.exists_eq_neg_of_nat (int.neg_nonpos_of_nonneg 
      (not_lt.mp ord_nonpos)),      
      simp only [neg_inj] at hs,
      have hf_coe : ↑((power_series.X)^s * F) = f,
      { rw [← f.single_order_mul_power_series_part, hs, hF, power_series.coe_mul,
        power_series.coe_pow, power_series.coe_X, ← single_pow] },
      rw ← hf_coe,
      obtain ⟨P, hP⟩ := exists_pol_int_val_lt K ((power_series.X)^s * F) γ,
      use ↑P,
      erw [← polynomial.coe_coe, ← coe_sub, laurent_series.coe_power_series,
        ← laurent_series.coe_algebra_map, valuation_of_algebra_map],
      exact hP },
end

lemma coe_range_dense : dense_range (coe : (ratfunc K) → (laurent_series K)) :=
begin
  rw dense_range_iff_closure_range,
  ext f,
  simp only [mem_closure_iff_symm_ball, set.mem_univ, iff_true, set.nonempty, set.mem_inter_iff,
    set.mem_range, set.mem_set_of_eq, exists_exists_eq_and],
  intros V hV h_symm,  
  rw [uniformity_eq_comap_neg_add_nhds_zero_swapped] at hV,
  obtain ⟨T, hT₀, hT₁⟩ := hV,
  obtain ⟨γ, hγ⟩ := valued.mem_nhds_zero.mp hT₀,
  obtain ⟨P, _⟩ := exists_ratfunc_val_lt K f γ,
  use P,
  apply hT₁,
  apply hγ,
  simpa only [set.mem_set_of_eq, add_comm, ← sub_eq_add_neg],
end

end dense

section comparison

open ratfunc


lemma ratfunc_mk_eq_mk' (f : (polynomial K)) (g : (polynomial K)) (hg : g ≠ 0) : (ratfunc.mk f g) = 
  is_localization.mk' (ratfunc K) f ⟨g, mem_non_zero_divisors_iff_ne_zero.2 hg⟩ :=
by simp only [mk_eq_div, is_fraction_ring.mk'_eq_div, set_like.coe_mk]

lemma ratfunc_mk_val (f : (polynomial K)) (g : polynomial K) (hg : g ≠ 0) : 
  (ideal_X K).valuation ( ratfunc.mk f g) =
  ((ideal_X K).int_valuation f) / ((ideal_X K).int_valuation g) :=
by simp only [ratfunc_mk_eq_mk' _ _ _ hg, valuation_of_mk', set_like.coe_mk]

--the lemma below exists almost in the same form as `polynomial.coe_coe` in `stuff`, and they 
-- should be merged
lemma ratfunc.coe_coe (f : polynomial K) : (↑(algebra_map (polynomial K) (ratfunc K) f) :
  (laurent_series K)) = (algebra_map (power_series K) (laurent_series K)) f :=
by {rw [ratfunc.coe_def, coe_alg_hom, lift_alg_hom_apply, denom_algebra_map f, map_one, div_one,
  num_algebra_map], refl}


lemma ratfunc_valuation_eq_laurent_series (P: (ratfunc K)) : (ideal_X K).valuation (P) =
  (power_series.ideal_X K).valuation ((↑P : (laurent_series K))) :=
begin
  apply ratfunc.induction_on' P,
  intros f g h,
  convert ratfunc_mk_val K f g h,
  rw ratfunc_mk_eq_mk' K f g h,
  have aux : (↑(is_localization.mk' (ratfunc K) f ⟨g, mem_non_zero_divisors_iff_ne_zero.2 h⟩) : 
    laurent_series K) = ((is_localization.mk' (laurent_series K) (↑f : (power_series K))
    ⟨g, mem_non_zero_divisors_iff_ne_zero.2 $ coe_ne_zero h⟩) : laurent_series K),
  { simp only [is_fraction_ring.mk'_eq_div, set_like.coe_mk, coe_div],
    congr;
    apply ratfunc.coe_coe K },
  rw aux,
  have := @valuation_of_mk' (power_series K) _ _ _ (laurent_series K) _ _ _
    (power_series.ideal_X K) ↑f ⟨g, mem_non_zero_divisors_iff_ne_zero.2 $ coe_ne_zero h⟩,
  convert this;
  apply pol_int_valuation_eq_power_series,
end

lemma coe_is_inducing : uniform_inducing (coe : (ratfunc K) → (laurent_series K)) :=
begin
  rw [uniform_inducing_iff, filter.comap],
  ext S,
  simp only [exists_prop, filter.mem_mk, set.mem_set_of_eq, uniformity_eq_comap_nhds_zero,
    filter.mem_comap],
  split,
  { rintros ⟨T, ⟨⟨R, ⟨hR, pre_R⟩⟩, pre_T⟩⟩,
    obtain ⟨d, hd⟩ := valued.mem_nhds.mp hR,
    use {P : (ratfunc K) | valued.v P < ↑d},
    { simp only [valued.mem_nhds, sub_zero],
      use d,
      refine subset_trans _ pre_T,
      rintros _ _,
      apply pre_R,
      apply hd,
      simp only,
      erw [set.mem_set_of_eq, sub_zero, ← ratfunc.coe_sub, ← ratfunc_valuation_eq_laurent_series],
      assumption, }},
  { rintros ⟨T, ⟨hT, pre_T⟩⟩,
    obtain ⟨d, hd⟩ := valued.mem_nhds.mp hT,
    let X := {f : (laurent_series K) | valued.v f < ↑d},
    use [(λ (x : laurent_series K × laurent_series K), x.snd - x.fst) ⁻¹' X, X],
    { simp only [valued.mem_nhds, sub_zero],
      use d },
    { simp only [set.preimage_set_of_eq],
      refine subset_trans _ pre_T,
      rintros _ _,
      apply hd,
      simp only,
      erw [set.mem_set_of_eq, sub_zero, ratfunc_valuation_eq_laurent_series, ratfunc.coe_sub],
      assumption }},
end

lemma unif_cont_coe : uniform_continuous (coe : (ratfunc K) → (laurent_series K)) :=
  (uniform_inducing_iff'.1 (coe_is_inducing K)).1

noncomputable!
def ratfunc_adic_compl_pkg : abstract_completion (ratfunc K) := uniform_space.completion.cpkg 

noncomputable!
def laurent_series_pkg : abstract_completion (ratfunc K) :=
{ space := laurent_series K,
  coe := coe,
  uniform_struct := infer_instance,
  complete := infer_instance,
  separation := infer_instance,
  uniform_inducing := coe_is_inducing K,
  dense := coe_range_dense K}

@[simp]
lemma laurent_series_coe (x : ratfunc K) : (laurent_series_pkg K).coe x =
  (↑x : laurent_series K) := rfl

noncomputable!
def extension_as_ring_hom := uniform_space.completion.extension_hom (coe_alg_hom K).to_ring_hom

@[reducible]
def ratfunc_adic_compl := adic_completion (ratfunc K) (ideal_X K)

instance : field (ratfunc_adic_compl K) := adic_completion.field (ratfunc K) (ideal_X K)

instance : algebra K (polynomial K) := infer_instance

instance valued_ratfunc_adic_compl : valued (ratfunc_adic_compl K) ℤₘ₀ :=
  @valued.valued_completion _ _ _ _ (ideal_X K).adic_valued

instance : uniform_space (ratfunc_adic_compl K) := infer_instance

@[reducible]
definition compare_pkg : (ratfunc_adic_compl K) ≃ᵤ laurent_series K :=
  compare_equiv (ratfunc_adic_compl_pkg K) (laurent_series_pkg K)

namespace abstract_completion

open_locale topology

variables {α β : Type*} [uniform_space α] [topological_space β]
variables (pkg : abstract_completion α) (pkg' : abstract_completion α) 

definition top_pkg : topological_space pkg.space := pkg.uniform_struct.to_topological_space

definition top_pkg' : topological_space pkg'.space := pkg'.uniform_struct.to_topological_space

local attribute [instance] top_pkg top_pkg'

include pkg pkg'

lemma extend_compare_extend [t3_space β] (f : α → β) (cont_f : continuous f) 
  (hf : ∀ a : pkg.space, filter.tendsto f (filter.comap pkg.coe (𝓝 a))
    (𝓝 ((pkg.dense_inducing.extend f) a))) :
    (pkg.dense_inducing.extend f) ∘ (pkg'.compare pkg) = (pkg'.dense_inducing.extend f) :=
begin
  have : ∀ (x : α), (((pkg.dense_inducing.extend f)) ∘ pkg'.compare pkg) (pkg'.coe x) = f x,
  { intro a,
    rw [function.comp_app, compare_coe],
    apply dense_inducing.extend_eq _ cont_f },
  refine (dense_inducing.extend_unique (abstract_completion.dense_inducing _) this _).symm,
  letI := pkg'.uniform_struct,
  letI := pkg.uniform_struct,
  refine continuous.comp _ (uniform_continuous_compare pkg' pkg).continuous,
  apply dense_inducing.continuous_extend,
  use λ a, ⟨(pkg.dense_inducing.extend f) a, hf a⟩,
end

end abstract_completion

-- noncomputable!
@[reducible]
definition laurent_series_ring_equiv : 
  (ratfunc_adic_compl K) ≃+* (laurent_series K) :=
{ map_mul' := (extension_as_ring_hom K (unif_cont_coe K).continuous).map_mul',
  map_add' := (extension_as_ring_hom K (unif_cont_coe K).continuous).map_add',
  .. compare_pkg K }

@[simp]
lemma laurent_series_ring_equiv_apply (x : (ratfunc_adic_compl K)) : laurent_series_ring_equiv K x =
  compare_equiv (ratfunc_adic_compl_pkg K) (laurent_series_pkg K) x := rfl

@[simp]
lemma laurent_series_ring_equiv_apply' (x : (ratfunc_adic_compl K)) : laurent_series_ring_equiv K x =
  (ratfunc_adic_compl_pkg K).compare (laurent_series_pkg K) x := rfl

@[simp]
lemma laurent_series_ring_equiv_symm_apply (x : (laurent_series K)) :
  (laurent_series_ring_equiv K).symm x = compare_equiv
    (laurent_series_pkg K) (ratfunc_adic_compl_pkg K) x :=
by simpa only [ring_equiv.apply_symm_apply]

lemma coe_X_compare : (laurent_series_ring_equiv K) (↑(@ratfunc.X K _ _) : (ratfunc_adic_compl K)) =
  (↑(@power_series.X K _) : (laurent_series K)) :=
by {rw [power_series.coe_X, ← ratfunc.coe_X, ← laurent_series_coe,
  ← abstract_completion.compare_coe], refl}

section power_series

instance : topological_space (laurent_series_pkg K).space :=
(laurent_series_pkg K).uniform_struct.to_topological_space

open filter abstract_completion
open_locale with_zero_topology topology

lemma val_laurent_series_equal_extension : (laurent_series_pkg K).dense_inducing.extend valued.v = 
  (@valued.v (laurent_series K) _ ℤₘ₀ _ _) :=
begin
  apply dense_inducing.extend_unique,
  { intro x,
    erw ratfunc_valuation_eq_laurent_series K x,
    refl, },
  { exact @valued.continuous_valuation (laurent_series K) _ ℤₘ₀ _ _ },
end

lemma aux_val (a : ((ideal_X K).adic_completion (ratfunc K))) : 
  tendsto (@valued.v (ratfunc K) _ ℤₘ₀ _ _) (comap coe (𝓝 a)) (𝓝 (valued.v a : ℤₘ₀)) :=
begin
 set ψ := @valued.v (ratfunc K) _ ℤₘ₀ _ _ with hψ,
 let := @valued.is_topological_valuation ((ideal_X K).adic_completion (ratfunc K)) _ ℤₘ₀ _ _,
 by_cases ha : a = 0,
  { rw tendsto_def,
    intros S hS,
    simp only [mem_comap, exists_prop],
    rw [ha, map_zero, (with_zero_topology.has_basis_nhds_zero).1 S] at hS,
    obtain ⟨γ, γ_ne_zero, γ_le⟩ := hS,
    use {t | valued.v t < γ},
    split,
    { rw [ha, this],
      use units.mk0 γ γ_ne_zero,
      rw units.coe_mk0 },
    { simp only [set.preimage_set_of_eq, valued.valued_completion_apply, hψ],
      apply set.preimage_mono γ_le }},
    { rw [with_zero_topology.tendsto_of_ne_zero ((valuation.ne_zero_iff valued.v).mpr ha), hψ, 
        filter.eventually_comap, filter.eventually, valued.mem_nhds],
      simp only [set.set_of_subset_set_of],
      set γ := (valued.v a) / ((multiplicative.of_add (1 : ℤ)) : ℤₘ₀) with h_aγ,
      have γ_ne_zero : γ ≠ 0,
      { simpa only [ne.def, _root_.div_eq_zero_iff, valuation.zero_iff, with_zero.coe_ne_zero,
          or_false] },
      use units.mk0 γ γ_ne_zero,
      intros y val_y b diff_b_y,
      replace val_y : valued.v y = valued.v a,
      { refine valuation.map_eq_of_sub_lt _ (val_y.trans _),
        rw [units.coe_mk0, h_aγ, ← with_zero.coe_unzero ((valuation.ne_zero_iff valued.v).mpr ha),
          ← with_zero.coe_div, with_zero.coe_lt_coe, div_lt_self_iff, ← of_add_zero,
          multiplicative.of_add_lt],
        exact int.zero_lt_one },
      rwa [← valued.extension_extends, diff_b_y] }, 
end

lemma valuation_compare (f : laurent_series K) : (@valued.v (ratfunc_adic_compl K) _ ℤₘ₀ _ _) 
  ((laurent_series_pkg K).compare (ratfunc_adic_compl_pkg K) f) = 
  (valued.v f) :=
by simpa only [← val_laurent_series_equal_extension, ← extend_compare_extend
    (ratfunc_adic_compl_pkg K) (laurent_series_pkg K) (@valued.v (ratfunc K) _ ℤₘ₀ _ _)
      (valued.continuous_valuation) (aux_val K)] using rfl


@[reducible]
definition power_series_as_subring : subring (laurent_series K) :=
ring_hom.range (hahn_series.of_power_series ℤ K)

@[reducible]
definition power_series_equiv_subring : power_series K ≃+* power_series_as_subring K :=
begin
  rw [power_series_as_subring, ring_hom.range_eq_map],
  use subring.top_equiv.symm.trans (subring.equiv_map_of_injective _
    (hahn_series.of_power_series ℤ K) (hahn_series.of_power_series_injective))
end

lemma val_le_one_iff_eq_coe (f : laurent_series K) : valued.v f ≤ (1 : ℤₘ₀) ↔
  ∃ (F : power_series K), ↑F = f :=
begin
  rw [← with_zero.coe_one, ← of_add_zero, ← neg_zero, valuation_le_iff_coeff_zero_of_lt],
  refine ⟨λ h, ⟨power_series.mk (λ n, f.coeff n), _⟩, _⟩,
  ext (_ | n),
  { simp only [int.of_nat_eq_coe, laurent_series.coeff_coe_power_series, coeff_mk] },
  simp only [h -[1+n] (int.neg_succ_lt_zero n)],
  swap,
  rintros ⟨F, rfl⟩ _ _,
  all_goals { apply hahn_series.emb_domain_notin_range,
              simp only [nat.coe_cast_add_monoid_hom, rel_embedding.coe_fn_mk,
              function.embedding.coe_fn_mk, set.mem_range, not_exists, int.neg_succ_lt_zero],
              intro},
  linarith,
  linarith [(int.neg_succ_lt_zero n)],--can be golfed
end

lemma val_le_of_add_neg_zero_iff_eq_coe (f : laurent_series K) :
  valued.v f ≤ ↑(multiplicative.of_add (-0 : ℤ)) ↔ ∃ (F : power_series K), ↑F = f :=
by rw [neg_zero, of_add_zero, with_zero.coe_one, val_le_one_iff_eq_coe]


lemma mem_integers_of_power_series (F : (power_series K)) : (laurent_series_ring_equiv K).symm F ∈ 
  (ideal_X K).adic_completion_integers (ratfunc K) := sorry

-- lemma exists_power_series_of_mem_integers' {f : (laurent_series K)}
--   (hf : (laurent_series_ring_equiv K).symm f ∈ (ideal_X K).adic_completion_integers (ratfunc K)) : 
--   ∃ F : (power_series K), f = ↑F := sorry

lemma exists_power_series_of_mem_integers {x : (ratfunc_adic_compl K)}
  (hx : x ∈ (ideal_X K).adic_completion_integers (ratfunc K)) : 
  ∃ F : (power_series K), (laurent_series_ring_equiv K).symm F = x := sorry

lemma power_series_ext_subring : (subring.map (laurent_series_ring_equiv K).symm.to_ring_hom
    (power_series_as_subring K)) = ((ideal_X K).adic_completion_integers (ratfunc K)).to_subring :=
begin
  ext x,
  -- simp only [subring.mem_map, exists_prop, valuation_subring.mem_to_subring, 
  --   mem_adic_completion_integers],
  split,
  { rintros ⟨f, ⟨F, coe_F⟩, h_fF⟩,
    simp only [valuation_subring.mem_to_subring, ← h_fF, ← coe_F],
    apply mem_integer_of_power_series },

  { intro H,
    -- set f := (laurent_series_ring_equiv K) x with hf,
    -- have hx : x = (laurent_series_ring_equiv K).symm f, sorry,
    -- rw hx at H,
    -- simp only [valuation_subring.mem_to_subring] at h,
    obtain ⟨F, hF⟩ := exists_power_series_of_mem_integers K H,
    simp only [equiv.to_fun_as_coe, uniform_equiv.coe_to_equiv, exists_exists_eq_and,
      uniform_equiv.coe_symm_to_equiv, subring.mem_map, equiv.inv_fun_as_coe],
    exact ⟨F, ⟨F, rfl⟩, hF⟩,
    
    -- exact ⟨F, ⟨⟨F, rfl⟩, by erw [← hF, ← hx]⟩⟩,


  },

  -- { rintros ⟨f, ⟨F, coe_F⟩, h_fF⟩,
  --   have : ((laurent_series_ring_equiv K).symm.to_ring_hom) f =
  --     (laurent_series_pkg K).compare (ratfunc_adic_compl_pkg K) f := rfl,
  --   rw [← h_fF, this, valuation_compare],
  --   rw val_le_one_iff_eq_coe,
  --   exact ⟨F, coe_F⟩ },
  -- { intro h,
  --   set f := (laurent_series_ring_equiv K) x with hf,
  --   have := valuation_compare K f,
  --   have hx : (laurent_series_pkg K).compare (ratfunc_adic_compl_pkg K)
  --     ((laurent_series_ring_equiv K) x) = x := congr_fun (inverse_compare (laurent_series_pkg K)
  --     (ratfunc_adic_compl_pkg K)) x,
  --   rw [hx] at this,
  --   rw this at h,
  --   obtain ⟨F, h_fF⟩ := (val_le_one_iff_eq_coe K f).mp h,
  --   use F,
  --   split,
  --   { rw [power_series_as_subring, ring_hom.mem_range],
  --     exact ⟨F, refl _⟩ },
  --   { -- simpa [h_fF, hf] using hx,--this works but seems slower
  --     rw [h_fF, hf],
  --     apply hx }},
end


@[reducible]
definition power_series_ring_equiv : (power_series K) ≃+* 
  ((ideal_X K).adic_completion_integers (ratfunc K)) :=
((power_series_equiv_subring K).trans (@ring_equiv.subring_map _ _ _ _ (power_series_as_subring K)
  (laurent_series_ring_equiv K).symm)).trans (ring_equiv.subring_congr (power_series_ext_subring K))

-- -- @[simp]
-- lemma power_series_ring_equiv_coe (G : power_series K) :
-- ((laurent_series_ring_equiv K).symm ↑G) = (power_series_ring_equiv K G) :=
-- begin
--   -- rw power_series_ext_subring,
--   -- rw power_series_ring_equiv,
--   apply congr_arg,
--   simp only [ring_equiv.to_mul_equiv_eq_coe, mul_equiv.to_equiv_eq_coe, mul_equiv.coe_to_equiv,
--     ring_equiv.coe_to_mul_equiv, subtype.val_eq_coe],
--   -- have := power_series_ext_subring K,
--   -- refl,
--   rw power_series_equiv_subring,
--   simp only [eq_mpr_eq_cast, cast_cast],
--   erw subring.top_equiv_symm_apply_coe,
--   simp only [ring_hom.to_fun_eq_coe],-- hahn_series.of_power_series_apply],
--   simp,
--   congr,
--   -- rw subring.top_equiv_symm_apply_coe,
-- end


end power_series

end comparison

end completion_laurent_series