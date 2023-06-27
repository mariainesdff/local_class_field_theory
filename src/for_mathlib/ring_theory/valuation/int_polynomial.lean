/-
Copyright (c) 2023 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import for_mathlib.ring_theory.valuation.algebra_instances

open_locale discrete_valuation

variables {K : Type*} [field K] (v : valuation K ℤₘ₀)

namespace valuation

open polynomial

open_locale polynomial

def int_polynomial {P : K[X]} (hP : ∀ n : ℕ, (P.coeff n) ∈ v.valuation_subring) :
  v.valuation_subring[X] := 
{ to_finsupp := 
  { support := P.support,
    to_fun := λ n, ⟨P.coeff n, hP n⟩,
    mem_support_to_fun := λ n, by rw [ne.def, ← subring.coe_eq_zero_iff, 
      set_like.coe_mk, mem_support_iff] }}

namespace int_polynomial

lemma coeff_eq {P : K[X]} (hP : ∀ n : ℕ, (P.coeff n) ∈ v.valuation_subring) (n : ℕ) :
  ↑((int_polynomial v hP).coeff n) = P.coeff n :=
rfl

lemma leading_coeff_eq {P : K[X]} (hP : ∀ n : ℕ, (P.coeff n) ∈ v.valuation_subring) :
  ↑((int_polynomial v hP).leading_coeff) = P.leading_coeff :=
rfl

lemma monic_iff {P : K[X]} (hP : ∀ n : ℕ, (P.coeff n) ∈ v.valuation_subring) :
  (int_polynomial v hP).monic ↔ P.monic :=
by rw [monic, monic, ← leading_coeff_eq, one_mem_class.coe_eq_one]

lemma nat_degree {P : K[X]} (hP : ∀ n : ℕ, (P.coeff n) ∈ v.valuation_subring) : 
  (int_polynomial v hP).nat_degree = P.nat_degree :=
rfl

variables {L : Type*} [field L] [algebra K L]

lemma eval₂_eq {P : K[X]} (hP : ∀ n : ℕ, (P.coeff n) ∈ v.valuation_subring) (x : L) : 
  eval₂ (algebra_map ↥(v.valuation_subring) L) x (int_polynomial v hP) = aeval x P :=
begin
  rw [aeval_eq_sum_range, eval₂_eq_sum_range],
  apply finset.sum_congr rfl,
  intros n hn,
  rw algebra.smul_def,
  refl, 
end

end int_polynomial

end valuation