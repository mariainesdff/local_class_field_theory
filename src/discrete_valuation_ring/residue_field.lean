/-
Copyright (c) 2023 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import discrete_valuation_ring.extensions
import number_theory.ramification_inertia
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

variables (K : Type u) [field K] [hv : valued K ℤₘ₀]

local notation `K₀` := hv.v.valuation_subring

include hv

variables (L : Type v) [field L] [algebra K L] 

-- TODO: move to DVR.basic/extensions
instance : no_zero_smul_divisors K₀ (integral_closure K₀ L) := 
{ eq_zero_or_eq_zero_of_smul_eq_zero := λ c x h,
  begin
    rw [algebra.smul_def, mul_eq_zero] at h,
    refine h.imp_left (λ hc, _),
    rw ← map_zero (algebra_map K₀ (integral_closure K₀ L)) at hc,
    exact is_fraction_ring.injective K₀ K ((algebra_map K L).injective (subtype.ext_iff.mp hc)),
  end }

def prime_factor' : ideal (integral_closure K₀ L) :=
(ideal.map (algebra_map K₀ (integral_closure K₀ L)) (local_ring.maximal_ideal K₀))

variables [is_discrete hv.v] [complete_space K] [finite_dimensional K L]

-- TODO: Without making this explicit the file times out. However the linter warns of a loop.
@[priority 10000]
instance dd : is_dedekind_domain (integral_closure K₀ L) := 
is_principal_ideal_ring.is_dedekind_domain (integral_closure (hv.v.valuation_subring) L)

@[priority 10000]
noncomputable! lemma ufd : unique_factorization_monoid (ideal(integral_closure K₀ L)) :=
@ideal.unique_factorization_monoid (integral_closure K₀ L) _ _ _

noncomputable! def ccm : cancel_comm_monoid_with_zero (ideal(integral_closure K₀ L)) :=
@ideal.cancel_comm_monoid_with_zero (integral_closure K₀ L) _ _ _

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

lemma prime_factor_coe_eq_max_ideal : (prime_factor K L : ideal (integral_closure K₀ L)) =
  local_ring.maximal_ideal (integral_closure K₀ L) :=
local_ring.eq_maximal_ideal (is_prime.to_maximal_ideal
  (prime.ne_zero (unique_factorization_monoid.prime_of_factor _ (bar K L).some_spec)))

instance [is_separable K L] : 
  is_noetherian K₀ (integral_closure K₀ L) :=
by exact is_integral_closure.is_noetherian K₀ K L (integral_closure K₀ L)

lemma foo : (residue_field (integral_closure K₀ L)) =
  ((integral_closure K₀ L) ⧸ (prime_factor K L : ideal (integral_closure K₀ L))) :=
by rw [residue_field, prime_factor_coe_eq_max_ideal]

def alg : algebra (residue_field K₀) (residue_field (integral_closure K₀ L)) := 
begin
  apply ideal.quotient.algebra_quotient_of_ramification_idx_ne_zero 
  (algebra_map K₀ (integral_closure K₀ L))
    (local_ring.maximal_ideal K₀) _,
  rw ←prime_factor_coe_eq_max_ideal,
  apply_instance, 
end

@[priority 900] -- linter
instance {A : Type*} [comm_ring A] [is_domain A] [discrete_valuation_ring A] : 
is_principal_ideal_ring A := by refine discrete_valuation_ring.to_is_principal_ideal_ring


noncomputable! def alg' : 
  algebra (residue_field K₀)
    ((integral_closure K₀ L) ⧸ (prime_factor K L : ideal (integral_closure K₀ L))) := 
ideal.quotient.algebra_quotient_of_ramification_idx_ne_zero (algebra_map _ _)
    (local_ring.maximal_ideal K₀) (prime_factor K L)

local attribute [instance] alg alg'

--TODO : This should be trivial but it gives a memory error.
noncomputable! def sadf : residue_field (integral_closure K₀ L) ≃ₗ[residue_field K₀]
    (integral_closure K₀ L) ⧸ (prime_factor K L : ideal (integral_closure K₀ L)) :=
sorry
/- { to_fun    := λ x, 
  begin
    sorry/- convert x,
    rw prime_factor_coe_eq_max_ideal, -/
  end,
  map_add'  := sorry,
  map_smul' := sorry,
  inv_fun   := λ x, 
  begin
    
    
    sorry/- convert x,
    rw ← prime_factor_coe_eq_max_ideal, -/
  end,
  left_inv  := sorry,
  right_inv := sorry } -/
. 

--TODO : Speed up!
noncomputable! lemma finite_dimensional_residue_field_of_integral_closure [is_separable K L] : 
  finite_dimensional (residue_field K₀) (residue_field (integral_closure K₀ L)) :=
begin
  rw @finite_dimensional.finite_dimensional_iff_of_rank_eq_nsmul (residue_field K₀) 
    (residue_field (integral_closure K₀ L)) _ _ _
    ((integral_closure K₀ L) ⧸ (prime_factor K L : ideal (integral_closure K₀ L))) _ _ 1
    one_ne_zero,
  /- exact @ideal.factors.finite_dimensional_quotient K₀ _ (integral_closure K₀ L) _
    (local_ring.maximal_ideal K₀) _ _ _ _ _ (prime_factor K L), -/
  exact ideal.factors.finite_dimensional_quotient (local_ring.maximal_ideal K₀) 
    (prime_factor K L),
  rw [nsmul_eq_mul, algebra_map.coe_one, one_mul],
  exact linear_equiv.rank_eq (sadf K L),
end
.


def finite_residue_field_of_integral_closure [is_separable K L] 
  (hres : fintype (local_ring.residue_field K₀)) :
  fintype (local_ring.residue_field (integral_closure K₀ L)) :=
begin
  letI := finite_dimensional_residue_field_of_integral_closure K L,
  exact /- fintype.finite -/ (module.fintype_of_fintype (finite_dimensional.fin_basis 
    (local_ring.residue_field K₀) (local_ring.residue_field (integral_closure K₀ L)))),
end

def finite_residue_field_of_unit_ball [is_separable K L] 
  (hres : fintype (local_ring.residue_field K₀)) :
 fintype (local_ring.residue_field (extension K L).valuation_subring) :=
@fintype.of_equiv _ _ (finite_residue_field_of_integral_closure K L hres) 
  (local_ring.residue_field.map_equiv
  (ring_equiv.subring_congr 
  (discrete_valuation.extension.integral_closure_eq_integer K L))).to_equiv


end discrete_valuation

#lint