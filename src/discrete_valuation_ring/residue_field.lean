/-
Copyright (c) 2023 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import discrete_valuation_ring.extensions
import number_theory.ramification_inertia

namespace discrete_valuation

open valuation discrete_valuation
open_locale discrete_valuation


variables (K : Type*) [field K] [hv : valued K ℤₘ₀] [is_discrete hv.v] [complete_space K]

local notation `K₀` := hv.v.valuation_subring

include hv

noncomputable!
definition finite_residue_field_of_integral_closure (L : Type*) [field L] [algebra K L]
[finite_dimensional K L] (hres : fintype (local_ring.residue_field K₀)) :
 fintype (local_ring.residue_field (integral_closure K₀ L)) :=
begin
  have := ideal.factors.finite_dimensional_quotient,
end

noncomputable!
definition finite_residue_field_of_unit_ball (L : Type*) [field L] [algebra K L]
[finite_dimensional K L] (hres : fintype (local_ring.residue_field K₀)) :
 fintype (local_ring.residue_field (w K L).valuation_subring) :=
@fintype.of_equiv _ _ (finite_residue_field_of_integral_closure K L hres) 
  (local_ring.residue_field.map_equiv
  (ring_equiv.subring_congr (integral_closure_eq_integer K L))).to_equiv


end discrete_valuation