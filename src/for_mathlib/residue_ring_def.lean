import topology.algebra.valued_field
import ring_theory.valuation.integers

namespace valuation

variables (K : Type*) [field K] 
variables {Γ₀ : Type*} [linear_ordered_comm_group_with_zero Γ₀]
variable [val : valued K Γ₀] 

include val

def open_ball_as_ideal : ideal (valuation.integer (val.v)) :=
{ carrier := {x : valued.v.integer | (@valued.v K _ _ _ _) ↑x < (1 : Γ₀)},
  add_mem' := sorry,
  zero_mem' := sorry,
  smul_mem' := sorry }
  
def residue_ring : Type* := (valuation.integer (val.v)) ⧸ (open_ball_as_ideal K)

instance : comm_ring (residue_ring K) := ideal.quotient.comm_ring _

end valuation


