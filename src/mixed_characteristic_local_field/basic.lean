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


def pi_equiv : K ≃ₗ[ℚ_[p]] (fin (finite_dimensional.finrank ℚ_[p] K) → ℚ_[p]) := 
begin
  apply finite_dimensional.linear_equiv.of_finrank_eq K 
    (fin (finite_dimensional.finrank ℚ_[p] K) → ℚ_[p]),
  simp only [finite_dimensional.finrank_fin_fun],
  exacts [mixed_char_local_field.to_finite_dimensional,
    finite_dimensional.finite_dimensional_pi ℚ_[p]],
end

def mixed_char_local_field.pi_topology : topological_space K := 
  topological_space.induced (pi_equiv p K) Pi.topological_space

-- -- lemma mixed_char_local_field.is_locally_compact : 
-- --   @locally_compact_space K (mixed_char_local_field.to_topological_space p K) := 
-- -- sorry

-- end valuation
-- end mixed_char_local_field

-- variables (E : Type*) [add_comm_group E] [module ℝ E] [comm_ring E] [algebra ℝ E]
--   [finite_dimensional ℝ E]

-- def real_pi_equiv : E ≃ₗ[ℝ] (fin (finite_dimensional.finrank ℝ E) → ℝ ) :=
-- begin
--   apply finite_dimensional.linear_equiv.of_finrank_eq E
--     (fin (finite_dimensional.finrank ℝ E) → ℝ),
--   simp only [finite_dimensional.finrank_fin_fun],
--   apply_instance,
--   exact finite_dimensional.finite_dimensional_pi ℝ,
-- end

-- def real_pi_topology : topological_space E := 
--   topological_space.induced (real_pi_equiv E) Pi.topological_space

-- def real_pi_homeo : @homeomorph E (fin (finite_dimensional.finrank ℝ E) → ℝ )
--   (real_pi_topology E) _ :=
-- begin
--   apply @homeomorph.mk _ _ (real_pi_topology E) _ (real_pi_equiv E).to_equiv,
--   have : @continuous _ _ _ (real_pi_topology E) (real_pi_equiv E).to_equiv.symm,
--   { rw continuous_iff_coinduced_le,
--     rw equiv.coinduced_symm,
--     suffices : (real_pi_topology E) = 
--       topological_space.induced (real_pi_equiv E) Pi.topological_space,
--     exact le_of_eq this,
--     refl},
--   exact this,
-- end

-- #exit

def pi_homeo : @homeomorph K (fin (finite_dimensional.finrank ℚ_[p] K) → ℚ_[p])
  (mixed_char_local_field.pi_topology p K)  _ :=
begin
  letI := mixed_char_local_field.pi_topology p K,
  have equiv_cont : continuous (pi_equiv p K).to_equiv,
  { rw [continuous_iff_le_induced],
    exact le_of_eq (refl _) },
  have symm_cont : continuous (pi_equiv p K).to_equiv.symm,
  { rw [continuous_iff_coinduced_le, equiv.coinduced_symm],
    exact le_of_eq (refl _) },
  apply homeomorph.mk (pi_equiv p K).to_equiv equiv_cont symm_cont
end 

lemma mixed_char_local_field.t2_space : @t2_space K (mixed_char_local_field.pi_topology p K):=
begin
  letI := mixed_char_local_field.pi_topology p K,
  exact homeomorph.t2_space (pi_homeo p K).symm,
end

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