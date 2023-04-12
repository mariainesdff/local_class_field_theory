import eq_characteristic.valuation
--import mixed_characteristic.valuation

import number_theory.class_number.function_field
--import number_theory.function_field
--import number_theory.number_field.basic



noncomputable theory

open_locale classical
/- 
namespace number_field

variables (L : Type*) [field L] [number_field L]
  (v : is_dedekind_domain.height_one_spectrum (ring_of_integers L))

def residue_char (v : is_dedekind_domain.height_one_spectrum (ring_of_integers L)) : ℕ := sorry 


instance : fact (nat.prime (residue_char L v)) :=
sorry

noncomputable! instance : mixed_char_local_field (residue_char L v)
  (is_dedekind_domain.height_one_spectrum.adic_completion L v) := sorry

end number_field -/

namespace function_field

open_locale polynomial

variables (p : ℕ) [fact (nat.prime p)]
/- variables (Fq F : Type) [field Fq] [fintype Fq] [field F]
variables [algebra Fq[X] F] [algebra (ratfunc Fq) F]
variables [is_scalar_tower Fq[X] (ratfunc Fq) F]
variables [function_field Fq F] [is_separable (ratfunc Fq) F]

#exit -/
--noncomputable example : is_scalar_tower (Fq[X]) (ratfunc Fq) L := sorry

--variables [function_field Fq L] [is_separable (ratfunc Fq) L]

variables (L : Type) [field L] [algebra 𝔽_[p][X] L]  [algebra (ratfunc 𝔽_[p]) L] 
noncomputable example : is_scalar_tower 𝔽_[p][X] (ratfunc 𝔽_[p]) L := sorry



--variables [function_field 𝔽_[p] L] [is_separable (ratfunc 𝔽_[p]) L]

noncomputable! lemma foo (A : ring_of_integers 𝔽_[p] L) : true := sorry
--[is_scalar_tower 𝔽_[p][X] (ratfunc 𝔽_[p]) L]
 -- (v : is_dedekind_domain.height_one_spectrum (ring_of_integers 𝔽_[p] L))

#exit

def residue_char (v : is_dedekind_domain.height_one_spectrum (ring_of_integers L)) : ℕ := sorry 


instance : fact (nat.prime (residue_char L v)) :=
sorry

noncomputable! instance : mixed_char_local_field (residue_char L v)
  (is_dedekind_domain.height_one_spectrum.adic_completion L v) := sorry

end function_field