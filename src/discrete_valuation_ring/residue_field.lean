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
.

open local_ring valuation --discrete_valuation
open_locale discrete_valuation classical

namespace discrete_valuation


variables (K : Type*) [field K] [hv : valued K ℤₘ₀] [is_discrete hv.v] [complete_space K]

local notation `K₀` := hv.v.valuation_subring

include hv

def prime_factor (L : Type*) [field L] [algebra K L] [finite_dimensional K L]  : 
  ((unique_factorization_monoid.factors (ideal.map (algebra_map K₀ (integral_closure K₀ L))
    (local_ring.maximal_ideal K₀))).to_finset) :=
sorry

lemma prime_factor_coe_eq_max_ideal (L : Type*) [field L] [algebra K L] [finite_dimensional K L] : 
  (prime_factor K L : ideal (integral_closure K₀ L)) = 
    local_ring.maximal_ideal (integral_closure K₀ L) :=
sorry

.

instance (L : Type*) [field L] [algebra K L] [finite_dimensional K L] [is_separable K L] : 
  is_noetherian K₀ (integral_closure K₀ L) :=
by exact is_integral_closure.is_noetherian K₀ K L (integral_closure K₀ L)

noncomputable! def alg (L : Type*) [field L] [algebra K L] [finite_dimensional K L] : 
  module (residue_field K₀) (residue_field ↥(integral_closure K₀ L)) := sorry

.

noncomputable! lemma finite_dimensional_residue_field_of_integral_closure (L : Type*) [field L] 
  [algebra K L] [finite_dimensional K L] [is_separable K L] :
  @finite_dimensional (residue_field K₀) (residue_field (integral_closure K₀ L)) _ _ 
  (alg K L) :=
begin
  letI := alg K L,
/-   letI : module (residue_field K₀)
    (↥(integral_closure K₀ L) ⧸ (prime_factor K L : ideal (integral_closure K₀ L))) :=
  sorry, -/
  have : finite_dimensional (K₀ ⧸ local_ring.maximal_ideal ↥(valued.v.valuation_subring))
   (↥(integral_closure ↥(valued.v.valuation_subring) L) ⧸ ↑(prime_factor K L)) := 
  @ideal.factors.finite_dimensional_quotient K₀ _ (integral_closure K₀ L) _
    (local_ring.maximal_ideal K₀) _ _ _ _ _ (prime_factor K L),
  sorry,
  /- have /- : finite_dimensional (residue_field K₀) 
    (((integral_closure K₀ L) ⧸ (prime_factor K L : ideal (integral_closure K₀ L))))  -/:= 
  @ideal.factors.finite_dimensional_quotient K₀ _ (integral_closure K₀ L) _
    (local_ring.maximal_ideal K₀) _ _ _ _ _ (prime_factor K L), -/
  set e : residue_field (integral_closure K₀ L) ≃ₗ[(residue_field K₀)] 
    ((integral_closure K₀ L)⧸(prime_factor K L : ideal (integral_closure K₀ L))) :=
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