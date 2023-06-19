/-
Copyright (c) 2023 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import discrete_valuation_ring.extensions
import eq_characteristic.basic

noncomputable theory

open is_dedekind_domain nnreal polynomial ratfunc multiplicative
open_locale eq_char_local_field nnreal discrete_valuation


namespace eq_char_local_field

.

variables (p : out_param (ℕ)) [hp : fact (p.prime)] 

include hp
variables (K : Type*) [field K] [eq_char_local_field p K]

-- TODO: come back after fixing the names in `dvr.extensions`

--TODO: How can I put this inside the proof of `valued`?
def foo : normed_field K := extension_normed_field 𝔽_[p]⟮⟮X⟯⟯ K

local attribute [instance] foo

-- NOTE: There is a diamond on 𝔽_[p]⟮⟮X⟯⟯, but by setting this priority lower, it seems
-- that Lean finds the correct instance.
@[priority 100] instance : valued K ℤₘ₀ := --valued.mk' (w 𝔽_[p]⟮⟮X⟯⟯ K)
{ v := w 𝔽_[p]⟮⟮X⟯⟯ K,
  is_topological_valuation := λ U,
  begin
    rw metric.mem_nhds_iff,
    refine ⟨λ h, _, λ h, _⟩, 
    { obtain ⟨ε, hε, h⟩ := h,
      sorry
      /- use units.mk0 ⟨ε, le_of_lt hε⟩ (ne_of_gt hε),
      intros x hx,
      exact h (mem_ball_zero_iff.mpr hx)  -/},
    { obtain ⟨ε, hε⟩ := h,
      sorry
      /- use [(ε : ℝ), nnreal.coe_pos.mpr (units.zero_lt _)],
      intros x hx,
      exact hε  (mem_ball_zero_iff.mp hx) -/ },

    /- rw metric.mem_nhds_iff,
    refine ⟨λ h, _, λ h, _⟩, 
    { obtain ⟨ε, hε, h⟩ := h,
      use units.mk0 ⟨ε, le_of_lt hε⟩ (ne_of_gt hε),
      intros x hx,
      exact h (mem_ball_zero_iff.mpr hx) },
    { obtain ⟨ε, hε⟩ := h,
      use [(ε : ℝ), nnreal.coe_pos.mpr (units.zero_lt _)],
      intros x hx,
      exact hε  (mem_ball_zero_iff.mp hx) }, -/
  end,
  ..(uniform_space_extension (algebra.is_algebraic_of_finite 𝔽_[p]⟮⟮X⟯⟯ K)),
  ..non_unital_normed_ring.to_normed_add_comm_group }

local attribute [-instance] foo

@[priority 100] instance : complete_space K := extension_complete 𝔽_[p]⟮⟮X⟯⟯ K

instance : valuation.is_discrete (eq_char_local_field.with_zero.valued p K).v := 
is_discrete_of_finite 𝔽_[p]⟮⟮X⟯⟯ K

-- Without the `by apply`, it times out
instance : discrete_valuation_ring (𝓞 p K) := by apply dvr_of_finite_extension 𝔽_[p]⟮⟮X⟯⟯ K

variables {p}

lemma valuation_X_ne_zero : valued.v (algebra_map (ratfunc 𝔽_[p]) K X) ≠ (0 : ℤₘ₀) :=
by simp only [ne.def, _root_.map_eq_zero, ratfunc.X_ne_zero, not_false_iff] 

def ramification_index (K : Type*) [field K] [eq_char_local_field p K] : ℤ := 
  -(with_zero.unzero (valuation_X_ne_zero K)).to_add

localized "notation (name := ramification_index)
  `e` := eq_char_local_field.ramification_index" in eq_char_local_field 

end eq_char_local_field

namespace FpX_field_completion

open eq_char_local_field
open_locale eq_char_local_field

variables (p : out_param (ℕ)) [fact (p.prime)] 

lemma is_unramified : e 𝔽_[p]⟮⟮X⟯⟯ = 1 := 
begin
  have hX : (eq_char_local_field.with_zero.valued p (FpX_field_completion p)).v (X p) = 
    (of_add (-1 : ℤ)),
  { sorry },
  rw [ramification_index, neg_eq_iff_eq_neg, ← to_add_of_add (-1 : ℤ)],
  apply congr_arg,
  rw [← with_zero.coe_inj, ← hX, with_zero.coe_unzero],
  refl,
end
/- lemma is_unramified_ℚ_p : e ℚ_[p] = 1 :=
begin
  have hp : normalized_valuation ℚ_[p] p = (of_add (-1 : ℤ)),
  { have hp0 : (p : 𝓞 p ℚ_[p]) ≠ 0,
    { simp only [ne.def, nat.cast_eq_zero], exact nat.prime.ne_zero (_inst_1.1) }, --looks bad
    have hp_alg : (p : ℚ_[p]) = algebra_map (𝓞 p ℚ_[p]) ℚ_[p] (p : 𝓞 p ℚ_[p]) := rfl,
    simp only [normalized_valuation],
    rw [hp_alg, valuation_of_algebra_map],
    simp only [int_valuation, ← valuation.to_fun_eq_coe],
    rw [int_valuation_def_if_neg _ hp0, ← padic.open_unit_ball_def, associates.count_self],
    refl,
    { exact associates_irreducible (open_unit_ball ℚ_[p]), }}, -- so slow!
  rw [ramification_index, neg_eq_iff_neg_eq, ← to_add_of_add (-1 : ℤ)],
  apply congr_arg,
  rw [← with_zero.coe_inj, ← hp, with_zero.coe_unzero],
end
 -/

end FpX_field_completion
