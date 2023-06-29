/-
Copyright (c) 2023 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import discrete_valuation_ring.extensions
import mixed_characteristic.basic

noncomputable theory

open discrete_valuation is_dedekind_domain multiplicative nnreal padic_comparison
  padic_comparison.padic' polynomial ratfunc 
open_locale mixed_char_local_field nnreal discrete_valuation

namespace mixed_char_local_field

variables (p : out_param (ℕ)) [hp : fact (p.prime)] 

include hp
variables (K : Type*) [field K] [mixed_char_local_field p K]

-- NOTE: There is a diamond on 𝔽_[p]⟮⟮X⟯⟯, but by setting this priority lower, it seems
-- that Lean finds the correct instance.
@[priority 100] instance : valued K ℤₘ₀ := extension.valued (Q_p p) K

@[priority 100] instance : complete_space K := extension.complete_space (Q_p p) K

instance : valuation.is_discrete (mixed_char_local_field.with_zero.valued p K).v := 
extension.is_discrete_of_finite (Q_p p) K

instance : discrete_valuation_ring (𝓞 p K) := 
integral_closure.discrete_valuation_ring_of_finite_extension (Q_p p) K

variable {p}

lemma valuation_p_ne_zero : valued.v (p : K) ≠ (0 : ℤₘ₀) :=
by simp only [ne.def, valuation.zero_iff, nat.cast_eq_zero, hp.1.ne_zero, not_false_iff]

--TODO: turn into lemma
open multiplicative is_dedekind_domain.height_one_spectrum
def ramification_index (K : Type*) [field K] [mixed_char_local_field p K] : ℤ := 
  -(with_zero.unzero (valuation_p_ne_zero K)).to_add

localized "notation (name := ramification_index)
  `e` := mixed_char_local_field.ramification_index" in mixed_char_local_field

variable (p)

lemma padic'.mem_integers_iff (y : Q_p p) : y ∈ 𝓞 p (Q_p p) ↔ ‖ y ‖ ≤ 1 :=
begin
  rw [mem_ring_of_integers, is_integrally_closed.is_integral_iff, norm_le_one_iff_val_le_one],
  refine ⟨λ h, _, λ h, ⟨⟨y, h⟩, rfl⟩⟩,
  { obtain ⟨x, hx⟩ := h,
    rw [← hx, ← mem_adic_completion_integers],
    exact x.2, },
end

lemma is_unramified_Q_p : e (Q_p p) = 1 :=
begin
  sorry/- have hp : normalized_valuation ℚ_[p] p = (of_add (-1 : ℤ)),
  { have hp0 : (p : 𝓞 p ℚ_[p]) ≠ 0,
    { simp only [ne.def, nat.cast_eq_zero], exact nat.prime.ne_zero (_inst_1.1) }, --looks bad
    have hp_alg : (p : ℚ_[p]) = algebra_map (𝓞 p ℚ_[p]) ℚ_[p] (p : 𝓞 p ℚ_[p]) := rfl,
    simp only [normalized_valuation],
    rw [hp_alg, valuation_of_algebra_map],
    simp only [int_valuation, ← valuation.to_fun_eq_coe],
    rw [int_valuation_def_if_neg _ hp0, ← padic.open_unit_ball_def, associates.count_self],
    refl,
    { exact associates_irreducible (open_unit_ball ℚ_[p]), }}, -- so slow!
  rw [ramification_index, neg_eq_iff_eq_neg, ← to_add_of_add (-1 : ℤ)],
  apply congr_arg,
  rw [← with_zero.coe_inj, ← hp, with_zero.coe_unzero], -/
end

noncomputable! def padic'_int.equiv_valuation_subring : 
  Z_p p ≃+* ↥(mixed_char_local_field.with_zero.valued p (Q_p p)).v.valuation_subring := 
{ to_fun    := λ x,
  begin
    use x.1, 
    rw valuation.mem_valuation_subring_iff,
    /- erw ← mem_adic_completion_integers, 
    exact x.2, -/
    sorry,
  end,
  inv_fun   := sorry,
  left_inv  := sorry,
  right_inv := sorry,
  map_mul'  := sorry,
  map_add'  := sorry }

variable {p}

-- NOTE: The diamond for `valued` instances on Q_p shows up here.
lemma padic'_int.equiv_valuation_subring_comm :
  (algebra_map (mixed_char_local_field.with_zero.valued p (Q_p p)).v.valuation_subring K).comp 
    (padic'_int.equiv_valuation_subring p).to_ring_hom = algebra_map (Z_p p) K :=
sorry

end mixed_char_local_field
