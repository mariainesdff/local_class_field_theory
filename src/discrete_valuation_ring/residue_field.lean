/-
Copyright (c) 2023 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import discrete_valuation_ring.extensions
--import number_theory.ramification_inertia
import ring_theory.dedekind_domain.integral_closure


--
--Use `module.fintype_of_fintype` and `ideal.factors.finite_dimensional_quotient `
--and also `local_ring.residue_field.map_equiv`
.

open local_ring valuation --discrete_valuation
open_locale discrete_valuation classical

noncomputable theory

universes u v

namespace discrete_valuation

variables (K : Type u) [field K] [hv : valued K ℤₘ₀] [is_discrete hv.v] [complete_space K]

local notation `K₀` := hv.v.valuation_subring

include hv

.


variables (L : Type v) [field L] [algebra K L] [finite_dimensional K L]

/- instance : algebra (hv.v.valuation_subring) L := sorry

instance : discrete_valuation_ring ((integral_closure (hv.v.valuation_subring) L)) :=
sorry -/


-- Writing this instance speeds out ufd and ccm.
@[priority 10000]
instance dd : is_dedekind_domain (integral_closure K₀ L) := 
is_principal_ideal_ring.is_dedekind_domain (integral_closure (hv.v.valuation_subring) L)

@[priority 10000]
noncomputable! def ufd : unique_factorization_monoid (ideal(integral_closure K₀ L)) :=
@ideal.unique_factorization_monoid (integral_closure K₀ L) _ _ _
  --(discrete_valuation_ring_of_finite_extension K L)

noncomputable! def ccm : cancel_comm_monoid_with_zero (ideal(integral_closure K₀ L)) :=
@ideal.cancel_comm_monoid_with_zero (integral_closure K₀ L) _ _ _

/- lemma foo  (L : Type*) [field L] [algebra K L] [finite_dimensional K L]
: false :=
begin
  letI : @unique_factorization_monoid (ideal(integral_closure K₀ L)) (ccm K L) := ufd K L,
  let f := (@unique_factorization_monoid.factors (ideal(integral_closure K₀ L)) (ccm K L)  _ (ufd K L)
    (ideal.map (algebra_map K₀ (integral_closure K₀ L)) (local_ring.maximal_ideal K₀))),
  sorry
end
 -/
def prime_factor' : ideal (integral_closure K₀ L) :=
(ideal.map (algebra_map K₀ (integral_closure K₀ L)) (local_ring.maximal_ideal K₀))

-- TODO: move to DVR.basic/extensions
instance : no_zero_smul_divisors K₀ (integral_closure K₀ L) := 
{ eq_zero_or_eq_zero_of_smul_eq_zero := λ c x h,
  begin
    rw [algebra.smul_def, mul_eq_zero] at h,
    refine h.imp_left (λ hc, _),
    rw ← map_zero (algebra_map K₀ (integral_closure K₀ L)) at hc,
    exact is_fraction_ring.injective K₀ K ((algebra_map K L).injective (subtype.ext_iff.mp hc)),
  end }

lemma prime_factor'_ne_zero : 
  prime_factor' K L ≠ 0 :=
begin
  obtain ⟨π, hπ⟩:= discrete_valuation.exists_uniformizer hv.v, 
  rw [prime_factor', ideal.map, ne.def, ideal.zero_eq_bot, ideal.span_eq_bot],
  simp only [set.mem_image, set_like.mem_coe, mem_maximal_ideal, mem_nonunits_iff, 
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, not_forall, exists_prop],
  use [π, uniformizer_not_is_unit hv.v hπ],
  rw [map_eq_zero_iff _, ← subring.coe_eq_zero_iff],
  exact (uniformizer_ne_zero hv.v hπ),
  { exact no_zero_smul_divisors.algebra_map_injective _ _,}
end

--set_option profiler true
lemma prime_factor'_not_is_unit : ¬ is_unit (prime_factor' K L) :=
begin
  rw [prime_factor', ideal.map],
  rw ideal.is_unit_iff,
  rw ideal.eq_top_iff_one,
 -- intro h1,
  --rw ideal.mem_span_
  
  sorry 
end

-- With just an exact this times out every time
lemma bar : (∃ (p : ideal (integral_closure K₀ L)), 
  p ∈ unique_factorization_monoid.factors (prime_factor' K L)) :=
begin
  apply unique_factorization_monoid.exists_mem_factors,
  exact prime_factor'_ne_zero K L,
  apply prime_factor'_not_is_unit K L,
end

--set_option profiler true
noncomputable! def prime_factor (L : Type*) [field L] [algebra K L] [finite_dimensional K L] : 
  ((@unique_factorization_monoid.factors _ (ccm K L)  _ (ufd K L) 
    (ideal.map (algebra_map K₀ (integral_closure K₀ L)) 
    (local_ring.maximal_ideal K₀))).to_finset) :=
⟨(bar K L).some, multiset.mem_to_finset.mpr (bar K L).some_spec⟩
/- begin
  exact ⟨(bar K L).some, multiset.mem_to_finset.mpr (bar K L).some_spec⟩,
  /- set J : ideal (integral_closure K₀ L) := (ideal.map (algebra_map K₀ (integral_closure K₀ L)) 
    (local_ring.maximal_ideal K₀)) with hJ,
  have hJ0 : J ≠ 0 := sorry,
  have hJu : ¬ @is_unit (ideal (integral_closure K₀ L))  _ J := sorry,
  have h := @unique_factorization_monoid.exists_mem_factors (ideal (integral_closure K₀ L)) 
    (ccm K L)  _ (ufd K L) J hJ0, -/
  --cases (h _) with u hu,
  /- have h : finset.nonempty ((unique_factorization_monoid.factors (ideal.map (algebra_map K₀ (integral_closure K₀ L))
    (local_ring.maximal_ideal K₀))).to_finset),
  { rw finset.nonempty_iff_ne_empty, rw ne.def,
    rw multiset.to_finset_eq_empty,
    rw unique_factorization_monoid.factors_unique,
    sorry
  }, -/
  --sorry, --exact h.some
end -/

#exit

lemma prime_factor_coe_eq_max_ideal (L : Type*) [field L] [algebra K L] [finite_dimensional K L] : 
  (prime_factor K L : ideal (integral_closure K₀ L)) = 
    local_ring.maximal_ideal (integral_closure K₀ L) :=
begin
  sorry
end

#exit

instance (L : Type*) [field L] [algebra K L] [finite_dimensional K L] [is_separable K L] : 
  is_noetherian K₀ (integral_closure K₀ L) :=
by exact is_integral_closure.is_noetherian K₀ K L (integral_closure K₀ L)

noncomputable! def alg (L : Type*) [field L] [algebra K L] [finite_dimensional K L] : 
  module (residue_field K₀) (residue_field ↥(integral_closure K₀ L)) := sorry

instance {A : Type*} [comm_ring A] [is_domain A] [discrete_valuation_ring A] : 
is_principal_ideal_ring A := by refine discrete_valuation_ring.to_is_principal_ideal_ring

noncomputable! lemma finite_dimensional_residue_field_of_integral_closure (L : Type*) [field L] 
  [algebra K L] [finite_dimensional K L] [is_separable K L] : 
  @finite_dimensional (residue_field K₀) (residue_field (integral_closure K₀ L)) _ _ 
  (alg K L)  :=
begin
  letI := alg K L,
  letI h1 : is_dedekind_domain (integral_closure K₀ L) :=
  is_principal_ideal_ring.is_dedekind_domain _, 
  letI : field (K₀ ⧸ local_ring.maximal_ideal K₀),
  { exact (residue_field.field K₀) },
  /- letI : module (K₀ ⧸ local_ring.maximal_ideal K₀)
    (↥(integral_closure K₀ L) ⧸ (prime_factor K L : ideal (integral_closure K₀ L))),
  { sorry }, -/
  have : finite_dimensional (K₀ ⧸ local_ring.maximal_ideal K₀) _ /- 
    ((integral_closure K₀ L) ⧸ (prime_factor K L : ideal (integral_closure K₀ L)))  -/:= 
  @ideal.factors.finite_dimensional_quotient K₀ _ (integral_closure K₀ L) _
    (local_ring.maximal_ideal K₀) _ h1 _ _ _ (prime_factor K L),

  --convert this,
  /- letI := alg K L,
  letI h3 : discrete_valuation_ring (integral_closure K₀ L) :=
  integral_closure.discrete_valuation_ring_of_finite_extension K L,
  letI h2 : is_principal_ideal_ring (integral_closure K₀ L) :=
  discrete_valuation_ring.to_is_principal_ideal_ring,
  letI h1 : is_dedekind_domain (integral_closure K₀ L) :=
  discrete_valuation_ring.to_is_principal_ideal_ring.is_dedekind_domain _, 
  letI : field (K₀ ⧸ local_ring.maximal_ideal K₀),
  { exact (residue_field.field K₀) },
  letI : module (K₀ ⧸ local_ring.maximal_ideal K₀)
    (↥(integral_closure K₀ L) ⧸ (prime_factor K L : ideal (integral_closure K₀ L))),
  { sorry },
  have : @finite_dimensional 
    (K₀ ⧸ local_ring.maximal_ideal K₀) 
    ((integral_closure K₀ L) ⧸ (prime_factor K L : ideal (integral_closure K₀ L))) _ _ _ :=
  @ideal.factors.finite_dimensional_quotient K₀ _ (integral_closure K₀ L) _
    (local_ring.maximal_ideal K₀) _ _ _ _ _ (prime_factor K L), -/
  
  sorry
end


#exit
.

noncomputable! lemma finite_dimensional_residue_field_of_integral_closure (L : Type*) [field L] 
  [algebra K L] [finite_dimensional K L] [is_separable K L] :
  @finite_dimensional (residue_field K₀) (residue_field (integral_closure K₀ L)) _ _ 
  (alg K L) :=
begin
  letI := alg K L,
  letI h3 : discrete_valuation_ring (integral_closure K₀ L) :=
  dvr_of_finite_extension K L,
  letI h2 : is_principal_ideal_ring (integral_closure K₀ L) :=
  discrete_valuation_ring.to_is_principal_ideal_ring,
  letI h1 : is_dedekind_domain (integral_closure K₀ L) :=
  discrete_valuation_ring.to_is_principal_ideal_ring.is_dedekind_domain _,
  have : @finite_dimensional 
    (K₀ ⧸ local_ring.maximal_ideal K₀) 
    ((integral_closure K₀ L) ⧸ (prime_factor K L : ideal (integral_closure K₀ L))) :=
  sorry,

  /- letI h2 : is_principal_ideal_ring (integral_closure K₀ L) :=
  discrete_valuation_ring.to_is_principal_ideal_ring,
  letI h1 : is_dedekind_domain (integral_closure K₀ L) :=
  discrete_valuation_ring.to_is_principal_ideal_ring.is_dedekind_domain _,
/-   letI : module (residue_field K₀)
    (↥(integral_closure K₀ L) ⧸ (prime_factor K L : ideal (integral_closure K₀ L))) :=
  sorry, -/
  have : finite_dimensional 
    (↥(valued.v.valuation_subring) ⧸ local_ring.maximal_ideal ↥(valued.v.valuation_subring)) 
  (↥(integral_closure ↥(valued.v.valuation_subring) L) ⧸ ↑(prime_factor K L)) := 
  @ideal.factors.finite_dimensional_quotient K₀ _ (integral_closure K₀ L) _
    (local_ring.maximal_ideal K₀) _ _ _ _ _ (prime_factor K L),
  sorry,
  /- have /- : finite_dimensional (residue_field K₀) 
    (((integral_closure K₀ L) ⧸ (prime_factor K L : ideal (integral_closure K₀ L))))  -/:= 
  @ideal.factors.finite_dimensional_quotient K₀ _ (integral_closure K₀ L) _
    (local_ring.maximal_ideal K₀) _ _ _ _ _ (prime_factor K L), -/
  set e : residue_field (integral_closure K₀ L) ≃ₗ[(residue_field K₀)] 
    ((integral_closure K₀ L)⧸(prime_factor K L : ideal (integral_closure K₀ L))) := -/
  sorry,

  apply e.finite_dimensional,
  rw hK,
  unfold local_ring.residue_field,
    
  --erw prime_factor_coe_eq_max_ideal K L at this,
  
   
  sorry
end

#exit

noncomputable!
definition finite_residue_field_of_integral_closure (L : Type*) [field L] [algebra K L]
[finite_dimensional K L] (hres : fintype (local_ring.residue_field K₀)) :
 finite (local_ring.residue_field (integral_closure K₀ L)) :=
begin
  letI h1: is_noetherian ↥(valued.v.valuation_subring) 
    (integral_closure ↥(valued.v.valuation_subring) L) := sorry,
  have := @ideal.factors.finite_dimensional_quotient K₀ _ (integral_closure K₀ L) _
  (local_ring.maximal_ideal K₀) _ _ _ h1 _ (prime_factor K L), 
  --erw prime_factor_coe_eq_max_ideal K L at this,

   
  sorry
end

noncomputable!
definition finite_residue_field_of_unit_ball (L : Type*) [field L] [algebra K L]
[finite_dimensional K L] (hres : fintype (local_ring.residue_field K₀)) :
 fintype (local_ring.residue_field (w K L).valuation_subring) :=
@fintype.of_equiv _ _ (finite_residue_field_of_integral_closure K L hres) 
  (local_ring.residue_field.map_equiv
  (ring_equiv.subring_congr (integral_closure_eq_integer K L))).to_equiv


end discrete_valuation