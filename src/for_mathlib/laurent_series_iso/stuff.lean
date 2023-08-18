/-
Copyright (c) 2023 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import order.filter.basic
import algebra.order.hom.monoid
import for_mathlib.polynomial
import for_mathlib.power_series
import ring_theory.dedekind_domain.adic_valuation
import ring_theory.dedekind_domain.ideal
import ring_theory.laurent_series
import ring_theory.power_series.well_known

noncomputable theory

variables (K : Type*) [field K]

namespace polynomial

open ratfunc power_series

--it is now in the namespace `polynomial`
lemma fae_coe (P : polynomial K) : (P : laurent_series K) = (↑P : ratfunc K) :=
  by { erw [ratfunc.coe_def, ratfunc.coe_alg_hom, lift_alg_hom_apply, ratfunc.num_algebra_map,
    ratfunc.denom_algebra_map P, map_one, div_one], refl}

lemma coe_ne_zero {f : polynomial K} : f ≠ 0 → (↑f : (power_series K)) ≠ 0 :=
by simp only [ne.def, coe_eq_zero_iff, imp_self]

end polynomial

section valuation

open is_dedekind_domain.height_one_spectrum

lemma fae_int_valuation_apply {R : Type*} [comm_ring R] [is_domain R] [is_dedekind_domain R] 
  (v : is_dedekind_domain.height_one_spectrum R) {r : R} :
  int_valuation v r = int_valuation_def v r := refl _

end valuation

section normalized_factors

local attribute [instance] classical.prop_decidable

open multiplicity unique_factorization_monoid

/- TODO: This lemma is now in the file `ring_theory.dedekind_domain.ideal`, probably line 1446
[FAE, 7/7/23] Not quite sure, at any rate it is needed in the new version-/
--**USED** in `power_series_adic_completion`
lemma principal_ideal_ring.count_normalized_factors_eq_count_normalized_factors_span {R : Type*}
  [comm_ring R] [is_domain R] [is_principal_ideal_ring R] [normalization_monoid R]
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

--not sure
-- lemma count_normalized_factors_eq_associates_count {R : Type*} [comm_ring R]
--   [is_domain R] [is_principal_ideal_ring R] [normalization_monoid R] [unique_factorization_monoid R] 
--   {I J : ideal R} (hI : I ≠ 0)
--   (hJ : J.is_prime ) (hJ₀ : J ≠ ⊥) : multiset.count J (normalized_factors I) =
--   (associates.mk J).count (associates.mk I).factors :=
-- begin
--   replace hI : associates.mk I ≠ 0,
--   { apply associates.mk_ne_zero.mpr hI },
--   have hJ' : irreducible (associates.mk J),
--   { rw associates.irreducible_mk,
--     apply prime.irreducible,
--     apply ideal.prime_of_is_prime hJ₀ hJ },
--   apply ideal.count_normalized_factors_eq,
--   rw [← ideal.dvd_iff_le, ← associates.mk_dvd_mk, associates.mk_pow],
--   rw associates.dvd_eq_le,
--   rw associates.prime_pow_dvd_iff_le hI hJ',
--   { rw ← ideal.dvd_iff_le,
--     rw ← associates.mk_dvd_mk,
--     rw associates.mk_pow,
--     rw associates.dvd_eq_le,
--     rw associates.prime_pow_dvd_iff_le hI hJ',
--     linarith,
--   },
-- end

end normalized_factors

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

--not used, but symmetric
lemma prod_subset_diag_singleton_right {X : Type*} [nonempty X] {S T : set X} (hS : S.nonempty) (hT : T.nonempty) 
  (h_diag : S ×ˢ T ⊆ id_rel) : ∃ x, T = {x} :=
begin
  rw set.prod_subset_iff at h_diag,
  replace h_diag := λ x hx y hy, (h_diag y hy x hx).symm,
  exact prod_subset_diag_singleton_left hT hS ((prod_subset_iff).mpr h_diag),
end

--not used, but symmetric
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

section cauchy_discrete

open filter set
open_locale filter topology

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

end cauchy_discrete