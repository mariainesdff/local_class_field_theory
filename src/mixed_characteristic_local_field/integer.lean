/-
Copyright (c) 2022 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import number_theory.padics.padic_integers
import ring_theory.integral_closure
import mixed_characteristic_local_field.basic

noncomputable theory

-- set_option profiler true

-- open function
-- open_locale big_operators

-- For instances/lemmas about ℚₚ and ℤₚ
-- section padic

-- /-- `ℤ_[p]` with its usual ring structure is not a field. -/
-- lemma padic_int.not_is_field (p : ℕ) [hp : fact(nat.prime p)] : ¬ is_field ℤ_[p] :=
-- begin
--   rw ring.not_is_field_iff_exists_ideal_bot_lt_and_lt_top,
--   use ideal.span {(p : ℤ_[p])},
--   split,
--   { rw [bot_lt_iff_ne_bot, ne.def, ideal.span_singleton_eq_bot, nat.cast_eq_zero],
--     exact hp.1.ne_zero },
--   { rw [lt_top_iff_ne_top, ne.def, ideal.eq_top_iff_one, ideal.mem_span_singleton,
--       ← padic_int.norm_lt_one_iff_dvd, norm_one, not_lt], }
-- end

-- variables {p : ℕ} [fact(nat.prime p)]

-- lemma padic_int.coe_eq_zero (x : ℤ_[p]) : (x : ℚ_[p]) = 0  ↔ x = 0 :=
-- ⟨λ h, by {rw ← padic_int.coe_zero at h, exact subtype.coe_inj.mp h},
--     λ h, by {rw h, exact padic_int.coe_zero}⟩

-- end padic

variables (p : ℕ) [fact (p.prime)] 
variables (K: Type*) [field K] [mixed_char_local_field p K]
variables (L : Type*) [field L] [mixed_char_local_field p L]

-- /-- The ring of integers of a mixed characteristic local field is the integral closure of ℤ_[p]
--   in the local field. -/

instance to_int_algebra : algebra ℤ_[p] K := 
begin
  have hK : algebra ℚ_[p] K := infer_instance,
  exact (ring_hom.comp hK.to_ring_hom (@padic_int.coe.ring_hom p _)).to_algebra,
end 

-- just a stupid lemma to check that everything compiles well
lemma foo (a b : ℝ) : filter.tendsto (λ x, a * x + b) (nhds 0) (nhds b) :=
begin
  have h0 : filter.tendsto (id  : ℝ → ℝ) (nhds 0) (nhds 0),
  exact filter.tendsto_id,
  have h1 : filter.tendsto (λ x, a*x) (nhds 0) (nhds 0),
  convert filter.tendsto.const_mul a h0,
  simp only [mul_zero],
  have := filter.tendsto.const_add b h1,
  rw [add_zero] at this,
  simp only at this,
  simp_rw [add_comm b _] at this,
  exact this,
end


-- -- def ring_of_integers := {x : K // is_integral ℤ_[p] x}
def ring_of_integers := integral_closure ℤ_[p] K

notation `𝓞 ` := ring_of_integers

-- localized "notation (name := ring_of_integers)
--   `𝓞` := mixed_char_local_field.ring_of_integers" in mixed_char_local_field

lemma mem_ring_of_integers (x : K) : x ∈ 𝓞 p K ↔ is_integral ℤ_[p] x := iff.rfl

lemma is_integral_of_mem_ring_of_integers {x : K} (hx : x ∈ 𝓞 p K) :
  is_integral ℤ_[p] (⟨x, hx⟩ : 𝓞 p K) :=
begin
  obtain ⟨P, hPm, hP⟩ := hx,
  refine ⟨P, hPm, _⟩,
  rw [← polynomial.aeval_def, ← subalgebra.coe_eq_zero, polynomial.aeval_subalgebra_coe,
    polynomial.aeval_def,  subtype.coe_mk, hP],
end

lemma Z_p_is_ring_of_integers : 𝓞 p ℚ_[p] = ℤ_[p] :=

