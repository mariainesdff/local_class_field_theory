/-
Copyright (c) 2023 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import discrete_valuation_ring.extensions
import eq_characteristic.basic

noncomputable theory

open discrete_valuation is_dedekind_domain multiplicative nnreal polynomial ratfunc 
open_locale eq_char_local_field nnreal discrete_valuation

namespace eq_char_local_field

variables (p : out_param (ℕ)) [hp : fact (p.prime)] 

include hp
variables (K : Type*) [field K] [eq_char_local_field p K]

-- NOTE: There is a diamond on 𝔽_[p]⟮⟮X⟯⟯, but by setting this priority lower, it seems
-- that Lean finds the correct instance.
@[priority 100] instance : valued K ℤₘ₀ := extension.valued 𝔽_[p]⟮⟮X⟯⟯ K

@[priority 100] instance : complete_space K := extension.complete_space 𝔽_[p]⟮⟮X⟯⟯ K

instance : valuation.is_discrete (eq_char_local_field.with_zero.valued p K).v := 
extension.is_discrete_of_finite 𝔽_[p]⟮⟮X⟯⟯ K

instance : discrete_valuation_ring (𝓞 p K) := 
integral_closure.discrete_valuation_ring_of_finite_extension 𝔽_[p]⟮⟮X⟯⟯ K

variables {p}

lemma valuation_X_ne_zero : valued.v (algebra_map (ratfunc 𝔽_[p]) K X) ≠ (0 : ℤₘ₀) :=
by simp only [ne.def, _root_.map_eq_zero, ratfunc.X_ne_zero, not_false_iff] 

def ramification_index (K : Type*) [field K] [eq_char_local_field p K] : ℤ := 
  -(with_zero.unzero (valuation_X_ne_zero K)).to_add

localized "notation (name := ramification_index)
  `e` := eq_char_local_field.ramification_index" in eq_char_local_field 

end eq_char_local_field

namespace FpX_completion

open eq_char_local_field
open_locale eq_char_local_field

variables (p : out_param (ℕ)) [fact (p.prime)] 

lemma is_unramified : e 𝔽_[p]⟮⟮X⟯⟯ = 1 := 
begin
  have hX : (eq_char_local_field.with_zero.valued p (FpX_completion p)).v (X p) = 
    (of_add (-1 : ℤ)),
  { sorry }, -- NOTE: The valuation diamond causes trouble here
  rw [ramification_index, neg_eq_iff_eq_neg, ← to_add_of_add (-1 : ℤ)],
  apply congr_arg,
  rw [← with_zero.coe_inj, ← hX, with_zero.coe_unzero],
  refl,
end

end FpX_completion
