/-
Copyright (c) 2023 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import ring_theory.valuation.integers
import topology.algebra.valued_field

namespace valuation

open_locale discrete_valuation

variables (K : Type*) [field K] {Γ₀ : Type*} [linear_ordered_comm_group_with_zero Γ₀]
  [val : valued K Γ₀] 

include val

def open_ball_as_ideal : ideal (valuation.integer (val.v)) :=
{ carrier   := {x : valued.v.integer | (@valued.v K _ _ _ _) ↑x < (1 : Γ₀)},
  add_mem'  := λ x y hx hy, lt_of_le_of_lt (map_add_le_max' _ _ _) (max_lt_iff.mpr ⟨hx, hy⟩),
  zero_mem' := by simp only [set.mem_set_of_eq, algebra_map.coe_zero, map_zero, zero_lt_one],
  smul_mem' := λ c x hx,
  begin
    simp only [algebra.id.smul_eq_mul, set.mem_set_of_eq, subring.coe_mul, map_mul] at *,
    apply lt_of_le_of_lt (mul_le_mul_right' c.prop (valued.v (x : K))),
    rw one_mul,
    exact hx,
  end }
  
def residue_ring : Type* := (valuation.integer (val.v)) ⧸ (open_ball_as_ideal K)

instance : inhabited (valuation.residue_ring K) := ⟨ideal.quotient.mk _ 0⟩

instance : comm_ring (residue_ring K) := ideal.quotient.comm_ring _

end valuation