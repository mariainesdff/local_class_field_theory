/-
Copyright (c) 2023 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import eq_characteristic.valuation
import mixed_characteristic.valuation
import number_theory.function_field
import number_theory.number_field.basic

noncomputable theory

open_locale classical

namespace number_field

variables (L : Type*) [field L] [number_field L]
  (v : is_dedekind_domain.height_one_spectrum (ring_of_integers L))

definition residue_char (v : is_dedekind_domain.height_one_spectrum (ring_of_integers L)) : ℕ := sorry 

instance : fact (nat.prime (residue_char L v)) :=
sorry

noncomputable! instance adic_completion.mixed_char_local_field : 
  mixed_char_local_field (residue_char L v)
    (is_dedekind_domain.height_one_spectrum.adic_completion L v) := sorry

end number_field 

namespace function_field

open_locale polynomial

variables (p : ℕ) [fact (nat.prime p)]

variables (L : Type) [field L] [h_alg : algebra 𝔽_[p][X] L]  [algebra (ratfunc 𝔽_[p]) L] 
  [is_scalar_tower 𝔽_[p][X] (ratfunc 𝔽_[p]) L] [function_field 𝔽_[p] L]
  [is_separable (ratfunc 𝔽_[p]) L]
variables (v : is_dedekind_domain.height_one_spectrum (@ring_of_integers 𝔽_[p] L _ _ h_alg))

noncomputable! lemma foo (A : @ring_of_integers 𝔽_[p] L _ _ h_alg) : true := sorry

definition residue_char (v : is_dedekind_domain.height_one_spectrum
  (@ring_of_integers 𝔽_[p] L _ _ h_alg)) : ℕ := sorry 


instance : fact (nat.prime (residue_char p L v)) :=
sorry

noncomputable! instance adic_completion.eq_char_local_field : 
  eq_char_local_field (residue_char p L v)
    (is_dedekind_domain.height_one_spectrum.adic_completion L v) := sorry

end function_field