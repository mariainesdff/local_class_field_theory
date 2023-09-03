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

definition integer_ideal_below
  (v : is_dedekind_domain.height_one_spectrum (ring_of_integers L)) : (ideal ℤ) :=
v.as_ideal.comap (algebra_map ℤ (ring_of_integers L))

instance is_prime_integer_ideal_below : (integer_ideal_below L v).is_prime :=
v.as_ideal.comap_is_prime (algebra_map ℤ (ring_of_integers L))

lemma integer_ideal_below_ne_bot :(integer_ideal_below L v) ≠ ⊥ :=
begin
  obtain ⟨⟨x, x_int⟩, h_mem, ne_zero⟩ := (submodule.ne_bot_iff _).mp v.ne_bot,
  refine ideal.comap_ne_bot_of_algebraic_mem ne_zero h_mem (is_integral.is_algebraic _ _),
  exact number_field.is_integral_of_mem_ring_of_integers x_int,
end 

@[reducible]
definition residue_char (v : is_dedekind_domain.height_one_spectrum (ring_of_integers L)) : ℕ :=
(submodule.is_principal.generator (integer_ideal_below L v)).nat_abs

instance : fact (nat.prime (residue_char L v)) :=
begin
  rw [residue_char, ← int.prime_iff_nat_abs_prime],
  apply fact.mk,
  exact submodule.is_principal.prime_generator_of_is_prime (integer_ideal_below L v)
    (integer_ideal_below_ne_bot L v),
end

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


-- **FAE* What was the point of this `foo`?
-- noncomputable! lemma foo (A : @ring_of_integers 𝔽_[p] L _ _ h_alg) : true := sorry

-- **FAE** For the `residue_char` of an `equal_char` field, I think we can simply define it to be
-- `p`, no?
@[reducible]
definition residue_char (v : is_dedekind_domain.height_one_spectrum
  (@ring_of_integers 𝔽_[p] L _ _ h_alg)) : ℕ := p 


instance : fact (nat.prime (residue_char p L v)) := infer_instance


noncomputable!
definition algebra_over_completion : algebra (FpX_completion p) L := sorry


lemma is_finite_dimensional : @finite_dimensional (FpX_completion p) L _ _
  (@algebra.to_module _ _ _ _ (algebra_over_completion p L)) := sorry


noncomputable!
instance adic_completion.eq_char_local_field : 
-- definition adic_completion.eq_char_local_field : 
  eq_char_local_field (residue_char p L v)
    (is_dedekind_domain.height_one_spectrum.adic_completion L v) := sorry
-- { smul := 
--   begin
--     sorry,
--   end,
--   to_fun := sorry,
--   map_one' := sorry,
--   map_mul' := sorry,
--   map_zero' := sorry,
--   map_add' := sorry,
--   commutes' := sorry,
--   smul_def' := sorry,
--   to_finite_dimensional := is_finite_dimensional p L, }
  

end function_field