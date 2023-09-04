/-
Copyright (c) 2023 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import discrete_valuation_ring.extensions

noncomputable theory

open finite_dimensional valuation 

open_locale discrete_valuation 

namespace discrete_valuation

section complete

variables {K : Type*} [field K] [hv : valued K ℤₘ₀] [is_discrete hv.v] {L : Type*} [field L] 
  [algebra K L] [complete_space K] 

include hv

namespace integral_closure

--FROM NOW ON WE SHOULD THINK IF WE WANT TO KEEP THESE RESULTS

lemma finrank_eq : 
  finrank hv.v.valuation_subring (integral_closure hv.v.valuation_subring L) = finrank K L :=
sorry

end integral_closure

end complete

end discrete_valuation