import field_theory.adjoin
import ring_theory.valuation.valuation_subring

/-!
# Minimal polynomials.

We prove some results about valuations of zero coefficients of minimal polynomials. 

Let `K` be a field with a valuation `v` and let `L` be a field extension of `K`.

# Main Results
* `coeff_zero` : for `x ∈ K` the valuation of the zeroth coefficient of the minimal polynomial
  of `algebra_map K L x` over `K` is equal to the valuation of `x`.
* `unit_pow_ne_zero` : for any unit `x : Lˣ`, we prove that a certain power of the valuation of
  zeroth coefficient of the minimal polynomial of `x` over `K` is nonzero. This lemma is helpful 
  for defining the valuation on `L` inducing `v`.
-/

open finite_dimensional minpoly polynomial 

open_locale discrete_valuation

variables {K : Type*} [field K] {Γ₀ : Type*} [linear_ordered_comm_group_with_zero Γ₀]
  (v : valuation K Γ₀) {L : Type*} [field L] [algebra K L]

namespace valuation

/- For `x ∈ K` the valuation of the zeroth coefficient of the minimal polynomial
of `algebra_map K L x` over `K` is equal to the valuation of `x`.-/
lemma coeff_zero (x : K) :
  v ((minpoly K (algebra_map K L x)).coeff 0) = v x :=
by rw [minpoly.eq_X_sub_C, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, valuation.map_neg]

lemma unit_ne_zero (x : Kˣ) : v x ≠ (0 : Γ₀) :=
by simp only [ne.def, valuation.zero_iff, units.ne_zero x, not_false_iff]

/- For any unit `x : Lˣ`, we prove that a certain power of the valuation of
  zeroth coefficient of the minimal polynomial of `x` over `K` is nonzero. This lemma is helpful 
  for defining the valuation on `L` inducing `v`.-/
lemma unit_pow_ne_zero [finite_dimensional K L] (x : Lˣ) :
  (v ((minpoly K x.1).coeff 0))^((finrank K L)/(minpoly K x.1).nat_degree) ≠ (0 : Γ₀) :=
begin
  have h_alg : algebra.is_algebraic K L := algebra.is_algebraic_of_finite K L,
  have hdeg : 0 < finrank K L / (minpoly K x.val).nat_degree,
  { exact nat.div_pos (nat_degree_le (is_algebraic_iff_is_integral.mp (h_alg x.val)))
      (nat_degree_pos (is_algebraic_iff_is_integral.mp (h_alg x.val))), },
  rw [ne.def, pow_eq_zero_iff hdeg, valuation.zero_iff],
  exact coeff_zero_ne_zero (is_algebraic_iff_is_integral.mp (h_alg x.val)) (units.ne_zero x),
  apply_instance,
end

end valuation
