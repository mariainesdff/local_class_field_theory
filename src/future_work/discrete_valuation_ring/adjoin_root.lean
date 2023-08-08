/-
Copyright (c) 2023 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import discrete_valuation_ring.extensions

namespace discrete_valuation_ring

variables {A : Type*} [comm_ring A] [is_domain A] [discrete_valuation_ring A]

namespace adjoin_root

lemma is_domain_of_irreducible {f : polynomial A} 
  (hf : irreducible (polynomial.map (algebra_map A (local_ring.residue_field A)) f)) :
  is_domain (adjoin_root f) :=
sorry

-- Ch. I, Section 6, Prop. 15 of Serre's "Local Fields"
lemma discrete_valuation_ring_of_irreducible {f : polynomial A} 
  (hf : irreducible (polynomial.map (algebra_map A (local_ring.residue_field A)) f)) :
  @discrete_valuation_ring (adjoin_root f) _ (is_domain_of_irreducible hf) :=
sorry

-- Ch. I, Section 6, Cor. 1 of Serre's "Local Fields"
lemma is_integral_closure_of_irreducible {f : polynomial A} 
  (hf : irreducible (polynomial.map (algebra_map A (local_ring.residue_field A)) f)) :
  is_integral_closure (adjoin_root f) A (fraction_ring (adjoin_root f)) :=
sorry

end adjoin_root

local notation `K` := fraction_ring A

variables (L : Type*) [field L] [algebra K L] [finite_dimensional K L] [algebra A L]
[is_scalar_tower A K L]

open finite_dimensional

-- Serre's Proposition 16 in Chapter I, Section 6: we may want the algebra instance to become an
-- explicit variable so that when we use the definition we do not need `@`.
noncomputable!
def integral_closure_equiv_algebra_adjoin
  (hB : discrete_valuation_ring (integral_closure A L))
  [algebra (local_ring.residue_field A) (@local_ring.residue_field _ _ hB.to_local_ring)]
  (hpb : power_basis (local_ring.residue_field A) (@local_ring.residue_field _ _ hB.to_local_ring))
  (hdeg : finrank K L = hpb.dim) (x : (integral_closure A L))
  (hx : ideal.quotient.mk (@local_ring.maximal_ideal _ _ hB.to_local_ring) x = hpb.gen) : 
  (integral_closure A L) ≃+* algebra.adjoin A ({x} : set (integral_closure A L)) := sorry

noncomputable!
def integral_closure_equiv_adjoin_root
  (hB : discrete_valuation_ring (integral_closure A L))
  [algebra (local_ring.residue_field A) (@local_ring.residue_field _ _ hB.to_local_ring)]
  (hpb : power_basis (local_ring.residue_field A) (@local_ring.residue_field _ _ hB.to_local_ring))
  (hdeg : finrank K L = hpb.dim) (x : (integral_closure A L))
  (hx : ideal.quotient.mk (@local_ring.maximal_ideal _ _ hB.to_local_ring) x = hpb.gen) : 
  (integral_closure A L) ≃+* adjoin_root (minpoly A x) := sorry

end discrete_valuation_ring