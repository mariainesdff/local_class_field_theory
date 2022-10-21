/-
Copyright (c) 2022 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import ring_theory.dedekind_domain.adic_valuation
import ring_theory.laurent_series
import ring_theory.power_series.well_known

open polynomial is_dedekind_domain.height_one_spectrum ratfunc sequentially_complete-- uniform_space
open_locale discrete_valuation uniformity

variables (K : Type*) [field K]

noncomputable theory

def ideal_X : is_dedekind_domain.height_one_spectrum (polynomial K) := 
{ as_ideal := ideal.span({X}),
  is_prime := by { rw ideal.span_singleton_prime, exacts [prime_X, X_ne_zero] },
  ne_bot   := by { rw [ne.def, ideal.span_singleton_eq_bot], exact X_ne_zero }} 


def completion_of_ratfunc  := adic_completion (ratfunc K) (ideal_X K)

instance : field (completion_of_ratfunc K) := adic_completion.field (ratfunc K) (ideal_X K)

instance : algebra K (polynomial K) := infer_instance

variable (F : completion_of_ratfunc K)

#check (quot.exists_rep F).some
#check (@adic_valued (polynomial K) _ _ _ (ratfunc K) _ _ _ (ideal_X K)).to_uniform_space

instance : uniform_space (ratfunc K) :=
  (@adic_valued (polynomial K) _ _ _ (ratfunc K) _ _ _ (ideal_X K)).to_uniform_space

def entourage : ℕ → set ((ratfunc K) × (ratfunc K)):= λ n,
  {x | ↑(multiplicative.of_add (n : ℤ)) ≤ ((ideal_X K).valuation x) } ×ˢ
  { x | ↑(multiplicative.of_add (n : ℤ)) ≤ ((ideal_X K).valuation x) }

lemma entourage_subset (n : ℕ) : entourage K n ∈ (𝓤 (ratfunc K)) := sorry

#check seq ((quot.exists_rep F).some).2 (entourage_subset K)

def isom : 
  -- adic_completion.field (ratfunc K) (ideal_X K) ≃ ℤ := sorry
  (completion_of_ratfunc K) ≃ (laurent_series K) :=
{ to_fun :=
  begin
  intro F,
  let φ : ℤ → K := λ m, 1,
  apply hahn_series.mk φ,
  have : set.is_pwo φ.support, sorry,
  exact this,
  end,
  inv_fun := sorry,
  left_inv := sorry,
  right_inv := sorry }

