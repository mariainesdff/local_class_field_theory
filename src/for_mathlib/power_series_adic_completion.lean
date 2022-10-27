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

instance : uniform_space (ratfunc K) :=
  (@adic_valued (polynomial K) _ _ _ (ratfunc K) _ _ _ (ideal_X K)).to_uniform_space


lemma foo : (nhds (0 : ratfunc K)).has_basis set.univ (λ n : ℕ,
  {F : (ratfunc K) | ↑(multiplicative.of_add (n : ℤ)) ≤ (ideal_X K).valuation F}) :=
begin
  sorry
end

-- def boo := filter.has_basis.uniformity_of_nhds_zero (foo K)

-- #check boo K

-- lemma boo_subset (n : ℕ) : (boo K n) ∈ (𝓤 (ratfunc K)) :=
-- variable (d : ℤ)
-- #check foo K

-- lemma uff : true := sorry
-- include K F

def ss (F : completion_of_ratfunc K) : ℕ → (ratfunc K) := seq ((quot.exists_rep F).some).2
    (λ n, @filter.has_basis.mem_of_mem _ _ _ _ _ n
    (filter.has_basis.uniformity_of_nhds_zero (foo K)) trivial)

variable (F : completion_of_ratfunc K)
#check ss K F
-- --   use this,
-- -- end
-- -- #check @filter.has_basis.mem_of_mem (ratfunc K) ℕ (nhds 0) (λ n, true) _ d (foo K)

-- -- #check boo

-- lemma boo_subset (n : ℕ) : (boo K n) ∈ (𝓤 (ratfunc K)) :=

-- def entourage : ℕ → set ((ratfunc K) × (ratfunc K)):= λ n,
--   {x | ↑(multiplicative.of_add (n : ℤ)) ≤ ((ideal_X K).valuation x) } ×ˢ
--   { x | ↑(multiplicative.of_add (n : ℤ)) ≤ ((ideal_X K).valuation x) }

-- example : add_group (ratfunc K) := 
-- begin
--   apply_instance,
-- end

-- -- local attribute [instance] topological_add_group.to_uniform_add_group


-- example (G : Type*) [_inst_1 : add_group G] [_inst_2 : topological_space G] [_inst_3 : topological_add_group G] :
--     𝓤 G = filter.comap (λ (p : G × G), p.snd - p.fst) (nhds 0) :=
-- begin
--   apply uniformity_eq_comap_nhds_zero',
-- end

-- lemma entourage_subset (n : ℕ) : entourage K n ∈ (𝓤 (ratfunc K)) :=
-- begin
--   rw uniformity_eq_comap_nhds_zero' (ratfunc K),
--   rw filter.mem_comap',
--   rw entourage,
--   simp,
--   rw mem_nhds_iff,
--   use {F : (ratfunc K) | ↑(multiplicative.of_add (n : ℤ)) ≤ (ideal_X K).valuation F},
--   split,
--   { simp only [set.set_of_subset_set_of],


--   },





  -- intro,
    -- have one : is_open ({y :
  --  ratfunc K | ∀ (a b : ratfunc K),
  --  b - a = y → (multiplicative.of_add (n : ℤ)) ≤ ((ideal_X K).valuation) a ∧
  --    (multiplicative.of_add (n : ℤ)) ≤ ((ideal_X K).valuation) b}),
  --     sorry,
  
-- end

-- #check seq ((quot.exists_rep F).some).2 (entourage_subset K)

def ss_int : ℤ → ratfunc K
|(n : nat) := ss K F n
| _ := 0

def isom : 
  -- adic_completion.field (ratfunc K) (ideal_X K) ≃ ℤ := sorry
  (completion_of_ratfunc K) ≃ (laurent_series K) :=
{ to_fun :=
  begin
  intro F,
  -- let φ : ℤ → K := ss_int K F,
  let φ : ℤ → K := λ n, 0,
  apply hahn_series.mk φ,
  have : set.is_pwo φ.support, sorry,
  exact this,
  end,
  inv_fun := sorry,
  left_inv := sorry,
  right_inv := sorry }

