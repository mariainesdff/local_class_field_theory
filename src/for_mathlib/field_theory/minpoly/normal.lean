/-
Copyright (c) 2023 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import field_theory.minpoly.is_integrally_closed
import field_theory.normal

namespace minpoly

variables {K L : Type*} [field K] [field L] [algebra K L] 

theorem degree_dvd [finite_dimensional K L] {x : L} (hx : is_integral K x) :
  (minpoly K x).nat_degree ∣ (finite_dimensional.finrank K L) :=
begin
  rw [dvd_iff_exists_eq_mul_left, ← intermediate_field.adjoin.finrank hx],
  use finite_dimensional.finrank ↥K⟮x⟯ L,
  rw [eq_comm, mul_comm],
  exact finite_dimensional.finrank_mul_finrank _ _ _,
end

variables (K L) (R : subring K) [is_integrally_closed R] [is_fraction_ring R K]
 
lemma minpoly_of_subring (x : integral_closure R L) :
  polynomial.map (algebra_map R K) (minpoly R x) = (minpoly K (x : L)) :=
by rw eq_comm; apply (minpoly.is_integrally_closed_eq_field_fractions K L
      (is_integral_closure.is_integral R L x))

end minpoly