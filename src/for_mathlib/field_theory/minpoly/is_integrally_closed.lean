import field_theory.minpoly.is_integrally_closed

/-!
# Minimal polynomials

This file contains lemmas about minimal polynomials, to be added to the mathlib file
`field_theory.minpoly.is_integrally_closed`.


# Main Results

* `degree_dvd` : if `x : L` is an integral element in a field extension `L` over `K`, then
  the degree of the minimal polynomial of `x` over `K` divides `[L : K]`.
* `minpoly_of_subring` : If `R` is an integrally closed subring of `K`, `K` is a fraction ring of 
  `R` and `x` belongs to the integral closure of `R` in `L`, then the minimal polynomial of `x` 
  over `K` agrees with its minimal polynomial over `R` (applying the appropriate algebra map). 
-/


namespace minpoly

variables {K L : Type*} [field K] [field L] [algebra K L] 

/-- If `x : L` is an integral element in a field extension `L` over `K`, then the degree of the
  minimal polynomial of `x` over `K` divides `[L : K]`.-/
theorem degree_dvd [finite_dimensional K L] {x : L} (hx : is_integral K x) :
  (minpoly K x).nat_degree ∣ (finite_dimensional.finrank K L) :=
begin
  rw [dvd_iff_exists_eq_mul_left, ← intermediate_field.adjoin.finrank hx],
  use finite_dimensional.finrank ↥K⟮x⟯ L,
  rw [eq_comm, mul_comm],
  exact finite_dimensional.finrank_mul_finrank _ _ _,
end

variables (K L) (R : subring K) [is_integrally_closed R] [is_fraction_ring R K]

/-- The minimal polynomial of `x` over `K` agrees with its minimal polynomial over `R`. -/
lemma minpoly_of_subring (x : integral_closure R L) :
  polynomial.map (algebra_map R K) (minpoly R x) = (minpoly K (x : L)) :=
by rw eq_comm; apply (minpoly.is_integrally_closed_eq_field_fractions K L
  (is_integral_closure.is_integral R L x))

end minpoly