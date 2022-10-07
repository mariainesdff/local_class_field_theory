/-
Copyright (c) 2022 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import number_theory.padics.padic_integers
import mixed_characteristic_local_field.integer

noncomputable theory

-- set_option profiler true

open function
open_locale big_operators

section open_unit_ball

variables (p : ℕ) [fact (p.prime)] 
variables (K: Type*) [field K] [mixed_char_local_field p K]

lemma mixed_char_local_field.int_t2_space : 
  @t2_space (𝓞 p K) (@subtype.topological_space K _
  (mixed_char_local_field.pi_topology p K)) := @subtype.t2_space K _
    (mixed_char_local_field.pi_topology p K) (mixed_char_local_field.t2_space p K)

def is_topologically_nilpotent (x : 𝓞 p K) : Prop :=
  filter.tendsto (λ n : ℕ, x^n) filter.at_top (@nhds (𝓞 p K) (@subtype.topological_space K
  (λ x, is_integral ℤ_[p] x) (mixed_char_local_field.pi_topology p K)) 0)

-- variable (K)

-- `FAE` : This lemma is certainly false
lemma is_topologically_nilpotent_iff_forall_i (x : 𝓞 p K) : is_topologically_nilpotent p K x ↔
  ∀ i : (fin (finite_dimensional.finrank ℚ_[p] K)),
    is_topologically_nilpotent p ℚ_[p] ((pi_equiv p K) x i) :=
begin
  sorry,
end

lemma is_topological_nilpotent_add (x y : 𝓞 p K) (hx : is_topologically_nilpotent x)
  (hy : is_topologically_nilpotent y) : is_topologically_nilpotent (x + y) :=
begin
  rw is_topologically_nilpotent_iff_forall_i at hx hy ⊢,
  intro i,
  specialize hx i,
  specialize hy i,
end

-- variable (p)

def unit_open_ball : ideal (𝓞 p K) :=
{ carrier := { x : 𝓞 p K | is_topologically_nilpotent x},
  add_mem' := 
  begin
  sorry
  end,
  zero_mem' := sorry,
  smul_mem' := sorry }

lemma mem_unit_open_ball {x : 𝓞 p K} :
  x ∈ unit_open_ball p K ↔ is_topologically_nilpotent x := iff.rfl

lemma unit_ball_pow_succ_le [mixed_char_local_field p K] (n : ℕ) :
  (unit_open_ball p K)^(n.succ) ≤ (unit_open_ball p K)^n :=
begin
  induction n,
  { simp only [pow_zero, ideal.one_eq_top, le_top] },
  { simp only [nat.succ_eq_add_one, pow_add] at n_ih ⊢,
    exact ideal.mul_mono_left n_ih}
end

lemma antitone_unit_ball_pow [mixed_char_local_field p K] :
  antitone (λ n : ℕ, (unit_open_ball p K)^n) := antitone_nat_of_succ_le (unit_ball_pow_succ_le p K)

def add_valuation_map (x : 𝓞 p K) : ℕ := 
Sup { n : ℕ | x ∈ (unit_open_ball p K)^n ∧ x ∉ (unit_open_ball p K)^(n + 1)}

lemma add_valuation_of_int (x : 𝓞 p K) : (add_valuation_map p K x) ≠ 0 :=
begin
  sorry,
end 


lemma add_valuation_map_one : add_valuation_map p K 1 = 0 :=
begin
  suffices h : (1 : 𝓞 p K) ∉ (unit_open_ball p K),
  rw ← pow_one (unit_open_ball p K) at h,
  simp [add_valuation_map],
  { have : ∀ n : ℕ, 1 ≤ n → (1 : 𝓞 p K) ∉ (unit_open_ball p K)^n,
    { rintros n hn₁,
      have := (antitone_unit_ball_pow p K).imp hn₁,
      intro H,
      exact h (this H),
    },
    rw nat.Sup_def,
    { simp only [nat.find_eq_zero, set.mem_set_of_eq, le_zero_iff, and_imp],
      rintros n hn -,
      by_contra' h_abs,
      replace h_abs : 1 ≤ n := nat.one_le_iff_ne_zero.mpr h_abs,
      exact (this n h_abs) hn },
    { use 0,
      rintros n ⟨hn, -⟩,
      by_contra' h_abs,
      replace h_abs : 1 ≤ n := nat.one_le_iff_ne_zero.mpr (ne_of_gt h_abs),
      exact (this n h_abs) hn},
  },
  rw unit_open_ball,
  simp only [submodule.mem_mk, set.mem_set_of_eq],
  rw is_topologically_nilpotent,
  simp_rw one_pow,
  have h1 : filter.tendsto (λ (n : ℕ), (1 : 𝓞 p K)) filter.at_top (@nhds (𝓞 p K)
    (@subtype.topological_space K _ (mixed_char_local_field.pi_topology p K)) 1) :=
    @tendsto_const_nhds (𝓞 p K) ℕ (@subtype.topological_space K _ 
    (mixed_char_local_field.pi_topology p K)) 1 filter.at_top,
  intro h0,
  haveI ht2 := (mixed_char_local_field.int_t2_space p K),
  have : (0 : 𝓞 p K) = 1,
  { letI : topological_space (𝓞 p K) := (@subtype.topological_space K _ 
      (mixed_char_local_field.pi_topology p K)),
    refine tendsto_nhds_unique' _ h0 h1,
    exact filter.at_top_ne_bot, },
  exact zero_ne_one this,
end

-- open_locale classical

-- def mixed_char_local_field.valuation : 
--   valuation (𝓞 p K) (with_zero (multiplicative ℤ)) :=
-- { to_fun := λ x,
--     if x = 0 then 0 else multiplicative.of_add (0),
--   map_zero'  := sorry,
--   map_one'   := sorry,
--   map_mul'   := sorry,
--   map_add_le_max' := sorry }
-- /- lemma exists_uniformizer [mixed_char_local_field p K] :
--   ∃ π : K, π ∈ unit_open_ball p K ∧ ¬ π ∈ (unit_open_ball p K)^2 :=
-- begin
--   sorry
-- end -/

-- /- 
-- * Topology on K + this is locally compact.
-- * Define normalized discrete valuation on K, using topological nilpotent elements.
-- * Unit ball = ring of integers
-- * Top. nilp. elements are a maximal ideal P in O_K
-- * Define ramification index e
-- * P^e = (p)
-- * Relate to norm (future)
-- -/
end open_unit_ball