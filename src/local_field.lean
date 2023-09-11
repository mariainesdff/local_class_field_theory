import discrete_valuation_ring.residue_field
import eq_characteristic.valuation
import mixed_characteristic.valuation

/-!
# Local fields
In this file we define the `class local_field` on a valued field `K`, requiring that it is 
* complete (with respect to the uniform structure induced by the valuation)
* that its valuation is discrete
* that the residue field of its unit ball is finite

## Main Definitions
* `local_field` is the key definition, see above.


## Main Results
* For an `eq_char_local_field p K` that is separable over `𝔽_[p]⟮⟮X⟯⟯` we provide an instance
  `local_field K`. The separability assumption is required to use some result in mathlib concerning
  the finiteness of the ring of integers.
* For a `mixed_char_local_field p K` we provide an instance `local_field K`.
-/


open valuation discrete_valuation
open_locale discrete_valuation

/-- The class `local_field`, extending `valued K ℤₘ₀` by requiring that `K` is complete, that the
valuation is discrete, and that the residue field of the unit ball is finite. -/
class local_field (K : Type*) [field K] extends valued K ℤₘ₀ :=
(complete : complete_space K)
(is_discrete : is_discrete (@valued.v K _ ℤₘ₀ _ _))
(finite_residue_field :
  fintype (local_ring.residue_field ((@valued.v K _ ℤₘ₀ _ _).valuation_subring)))

namespace eq_char_local_field

open FpX_completion

@[priority 100] noncomputable! instance (p : out_param ℕ) [fact(nat.prime p)] (K : Type*) [field K]
  [eq_char_local_field p K] [is_separable 𝔽_[p]⟮⟮X⟯⟯ K]: local_field K := 
{ complete             := eq_char_local_field.complete_space p K,
  is_discrete          := v.valuation.is_discrete p K,
  finite_residue_field := 
  begin
    apply finite_residue_field_of_unit_ball,
    apply FpX_int_completion.residue_field_fintype_of_completion,
  end,
  ..(eq_char_local_field.with_zero.valued p K) }

end eq_char_local_field

namespace mixed_char_local_field
open padic

@[priority 100] noncomputable instance (p : out_param ℕ) [fact(nat.prime p)] (K : Type*) [field K] 
  [mixed_char_local_field p K] : local_field K := 
{ complete             := mixed_char_local_field.complete_space p K,
  is_discrete          := v.valuation.is_discrete p K,
  finite_residue_field :=
  begin
    apply finite_residue_field_of_unit_ball,
    apply ring_of_integers.residue_field_fintype_of_completion,
  end,
  ..(mixed_char_local_field.with_zero.valued p K) }
  
end mixed_char_local_field

#lint