import number_theory.padics.padic_integers
import number_theory.padics.ring_homs

/-! # Padic Integers
In this file we construct an isomorphism between the residue field of `ℤ_[p]` and the type `zmod p`
of integers modulo `p`.
-/

variables (p : out_param ℕ) [fact (p.prime)]

namespace padic_int


/-- The isomorphism of the residue field of the `p`-adic integers with the finite field with `p`
elements -/
noncomputable
definition residue_field : local_ring.residue_field ℤ_[p] ≃+* (zmod p) := 
begin
  let α := ring_hom.quotient_ker_equiv_of_surjective
    (zmod.ring_hom_surjective (@padic_int.to_zmod p _)),
  rw padic_int.ker_to_zmod at α,
  use α, 
end

end padic_int