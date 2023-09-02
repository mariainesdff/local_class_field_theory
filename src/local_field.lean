/-
Copyright (c) 2023 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import discrete_valuation_ring.residue_field
import eq_characteristic.valuation
import from_mathlib.rank_one_valuation
import mixed_characteristic.valuation


open valuation
open_locale discrete_valuation

class local_field (K : Type*) [field K] extends valued K ℤₘ₀ :=
(complete : complete_space K)
(is_discrete : is_discrete (@valued.v K _ ℤₘ₀ _ _))
(finite_residue_field :
  fintype (local_ring.residue_field ((@valued.v K _ ℤₘ₀ _ _).valuation_subring)))

namespace eq_char_local_field

@[priority 100] noncomputable! instance (p : out_param ℕ) [fact(nat.prime p)] (K : Type*) [field K]
  [eq_char_local_field p K] : local_field K := 
{ complete             := eq_char_local_field.complete_space p K,
  is_discrete          := v.valuation.is_discrete p K,
  finite_residue_field := 
  begin
    sorry,
    -- haveI := residue_field_of_power_series 𝔽_[p],
    -- haveI : finite_dimensional (ratfunc (galois_field p 1)) K, sorry,
    -- haveI : is_separable (ratfunc (galois_field p 1)) K, sorry,--this must be added as assumption, I believe
    -- have := @discrete_valuation.finite_residue_field_of_unit_ball (ratfunc 𝔽_[p]) _ _ K _ _ _ _ _
    -- sorry,
  end,
  ..(eq_char_local_field.with_zero.valued p K) }

end eq_char_local_field

namespace local_field

end local_field

-- #exit

namespace mixed_char_local_field

--TODO: generalize is_discrete lemma to adic_valued completion
@[priority 100] noncomputable instance (p : out_param ℕ) [fact(nat.prime p)] (K : Type*) [field K] 
  [mixed_char_local_field p K] : local_field K := 
{ complete             := mixed_char_local_field.complete_space p K,
  is_discrete          := v.valuation.is_discrete p K,
  finite_residue_field := sorry,
  ..(mixed_char_local_field.with_zero.valued p K) }

end mixed_char_local_field

