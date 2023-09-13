import ring_theory.valuation.integers

/-! 
# Valutation of units

The main result of this file, `valuation_one_of_is_unit` is a generalization of
`valuation.integers.one_of_is_unit` with a slightly weaker assumption

-/

namespace valuation

variables {R : Type*} {Γ₀ : Type*} [comm_ring R] [linear_ordered_comm_group_with_zero Γ₀] 
variables {v : valuation R Γ₀} {O : Type*} [comm_ring O] [algebra O R]


lemma valuation_one_of_is_unit {x : O} (hx : is_unit x) (hv : ∀ x, v (algebra_map O R x) ≤ 1)
  : v (algebra_map O R x) = 1 :=
let ⟨u, hu⟩ := hx in le_antisymm (hv _) $
by { rw [← v.map_one, ← (algebra_map O R).map_one, ← u.mul_inv, ← mul_one (v (algebra_map O R x)),
  hu, (algebra_map O R).map_mul, v.map_mul], exact mul_le_mul_left' (hv (u⁻¹ : units O)) _ }

end valuation