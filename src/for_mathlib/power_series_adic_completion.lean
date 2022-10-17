/-
Copyright (c) 2022 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import ring_theory.dedekind_domain.adic_valuation
import ring_theory.laurent_series
import ring_theory.power_series.well_known

open polynomial is_dedekind_domain.height_one_spectrum ratfunc
open_locale discrete_valuation

variables (K : Type*) [field K]

noncomputable theory

-- instance : is_dedekind_domain (polynomial K) := infer_instance

-- noncomputable!

def ideal_X : is_dedekind_domain.height_one_spectrum (polynomial K) := 
{ as_ideal := ideal.span({X}),
  is_prime := by { rw ideal.span_singleton_prime, exacts [prime_X, X_ne_zero] },
  ne_bot   := by { rw [ne.def, ideal.span_singleton_eq_bot], exact X_ne_zero }} 

-- noncomputable 
-- def ratfunc_valued  : valued (ratfunc K) ℤₘ₀ :=
-- valued.mk' (ideal_X K).valuation

def completion_of_ratfunc  := adic_completion (ratfunc K) (ideal_X K)

instance : field (completion_of_ratfunc K) := adic_completion.field (ratfunc K) (ideal_X K)

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

