/-
Copyright (c) 2022 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import number_theory.padics.padic_integers

noncomputable theory

-- set_option profiler true

open function
open_locale big_operators

-- namespace mixed_char_local_field

/-- A mixed characteristic local field is a field which has characteristic zero and is finite
dimensional over `ℚ_[p]`, for some prime `p`. -/
class mixed_char_local_field (p : ℕ) [fact (p.prime)] (K : Type*) [field K]
  extends algebra ℚ_[p] K :=
[to_char_zero : char_zero K]
[to_finite_dimensional : finite_dimensional ℚ_[p] K] 

instance (p : ℕ) [fact (p.prime)] : mixed_char_local_field p ℚ_[p] := mixed_char_local_field.mk

-- namespace mixed_char_local_field
-- -- attribute [nolint dangerous_instance] mixed_char_local_field.to_char_zero

-- -- See note [lower instance priority]
-- -- attribute [priority 100, instance] mixed_char_local_field.to_char_zero
-- --   mixed_char_local_field.to_finite_dimensional

variables (p : ℕ) [fact (p.prime)] 
variables (K: Type*) [field K] [mixed_char_local_field p K]
variables (L : Type*) [field L] [mixed_char_local_field p L]


-- -- lemma foo (a b : ℝ) : filter.tendsto (λ x, a * x + b) (nhds 0) (nhds b) :=
-- -- begin
-- --   have h0 : filter.tendsto (id  : ℝ → ℝ) (nhds 0) (nhds 0),
-- --   exact filter.tendsto_id,
-- --   have h1 : filter.tendsto (λ x, a*x) (nhds 0) (nhds 0),
-- --   convert filter.tendsto.const_mul a h0,
-- --   simp only [mul_zero],
-- --   have := filter.tendsto.const_add b h1,
-- --   rw [add_zero] at this,
-- --   simp only at this,
-- --   simp_rw [add_comm b _] at this,
-- --   exact this,
-- -- end




-- open mixed_char_local_field

-- open_locale mixed_char_local_field filter


-- /- 
-- * Topology on K + this is locally compact.
-- * Define normalized discrete valuation on K, using topological nilpotent elements.
-- * Unit ball = ring of integers
-- * Top. nilp. elements are a maximal ideal P in O_K
-- * Define ramification index e
-- * P^e = (p)
-- * Relate to norm (future)
-- -/
-- end valuation