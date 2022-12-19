/-
Copyright (c) 2022 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import ring_theory.dedekind_domain.adic_valuation
import ring_theory.laurent_series
import ring_theory.power_series.well_known

open polynomial is_dedekind_domain.height_one_spectrum topological_space ratfunc sequentially_complete filter
open_locale discrete_valuation uniformity filter topological_space

-- open filter topological_space set classical uniform_space function
-- open_locale classical uniformity topological_space filter

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

-- instance : valued (completion_of_ratfunc K) ℤₘ₀ :=
--   @valued.valued_completion _ _ _ _ (ideal_X K).adic_valued

-- instance : uniform_space (completion_of_ratfunc K) := 
-- begin
--   apply_instance,
-- end
  -- is_dedekind_domain.height_one_spectrum.uniform_space_adic_completion (ratfunc K) _

lemma foo : (nhds (0 : ratfunc K)).has_basis set.univ (λ n : ℕ,
  {F : (ratfunc K) | ↑(multiplicative.of_add (n : ℤ)) ≤ (ideal_X K).valuation F}) :=
begin
  sorry
end

lemma foo' : (nhds (0 : ratfunc K)).has_basis set.univ (λ n : ℤ,
  {F : (ratfunc K) | ↑(multiplicative.of_add n) ≤ (ideal_X K).valuation F}) :=
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
#check filter.map (ratfunc.coe_alg_hom K) ((quot.exists_rep F).some).1



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

def ss_int : ℤ → laurent_series K
|(n : nat) := ss K F n
| _ := 0

lemma foo2 (α : Type*) (u : ℕ → α) (N : ℕ) (hu : ∀ m : ℕ, N ≤ m → u m = u N) :
  at_top.map u ≤ pure (u N) := --at_top.map u ≤ 𝓟 ({u N}) :=
begin
  simp only [le_pure_iff, mem_map, mem_at_top_sets, ge_iff_le, set.mem_preimage,
    set.mem_singleton_iff],
  exact ⟨N, hu⟩,
end

lemma bar (α : Type*) (u : ℕ → α) (N : ℕ) (H : at_top.map u ≤ pure (u N)) :
  ∃ d, ∀ m : ℕ, d ≤ m → u m = u d :=
  --  := --at_top.map u ≤ 𝓟 ({u N}) :=
begin
  -- intros m hm,
  -- simp only [le_pure_iff, mem_map, mem_at_top_sets, ge_iff_le, set.mem_preimage,
  --   set.mem_singleton_iff] at H,
  simp at H,
  obtain ⟨a, ha⟩ := H,
  use a,
  intros m hm,
  by_cases a ≤ N,
  { have : u a = u N,
    exact ha a (le_of_eq (refl _)),
    rw this,
    exact ha _ hm },
  { replace h : N < a, sorry, sorry,  },
  -- let A := min a N,
  -- have hm' : A ≤ m,
  -- simp * at *,
  -- apply ha,
  -- have := (le_of_eq (refl a)),
  -- specialize ha b (le_max_iff.mpr _),
  -- apply or.intro_left _, 
  -- exact this,
  
  -- simp only [this, true_or],
  -- have := (true_or (le_of_eq (refl a))),

  -- squeeze_simp [b],
  -- simp only [le_pure_iff, mem_map, mem_at_top_sets, ge_iff_le, set.mem_preimage,
  --   set.mem_singleton_iff],
  -- exact ⟨N, hu⟩,
end

def eventual_coeff (ℱ : filter (ratfunc K)) (h : cauchy ℱ) (d : ℤ) : K :=
-- ∃ (t : set (laurent_series K)), t ∈ ℱ.map (ratfunc.coe_alg_hom K) ∧ t ≠ ∅ ∧ (∀ F G : (laurent_series K), F ∈ t → G ∈ t → F.coeff d = G.coeff d),
  sorry

def temp_coeff : ℤ → (laurent_series K → K) := λ i F, F.coeff i

lemma eventually_eq_eventual_coeff (ℱ : filter (ratfunc K)) (h : cauchy ℱ) (d : ℤ) :
  -- ( T : set (completion_of_ratfunc K)) : 
  ∀ T ∈ ℱ, (ℱ.map (ratfunc.coe_alg_hom K)).map (temp_coeff K d) = (ℱ.map (ratfunc.coe_alg_hom K)).map (temp_coeff K d) :=
begin
  sorry,
end

example (X : Type*) [uniform_space X] (ℱ : filter X) (hF : cauchy ℱ) :
  ∃ x : uniform_space.completion X, ℱ.map coe ≤ 𝓝 x :=
begin
  refine complete_space.complete _,
  refine cauchy.map hF _,
  refine uniform_space.completion.uniform_continuous_coe X,
end

def set_fae (d : ℤ) : set (ratfunc K × ratfunc K) :=
  {P | ↑(multiplicative.of_add d) ≤ (ideal_X K).valuation (P.1 - P.2)}

lemma coeff_fae (d : ℤ) (x y : ratfunc K) (H : (x, y) ∈ (set_fae K d)) :
 (x : laurent_series K).coeff d = (y : laurent_series K).coeff d :=
begin
  sorry
end

lemma entourage_fae (d : ℤ) : set_fae K d ∈ 𝓤 (ratfunc K) :=
begin
  sorry,
end

instance discrete_fae : uniform_space K := ⊥

def eval_fae (d : ℤ) : ratfunc K → K := λ x : ratfunc K, (x : laurent_series K).coeff d

lemma unif_cnts_fae (d : ℤ) : uniform_continuous (eval_fae K d) :=
-- begin
  sorry
-- end

def eval_compl_fae (d : ℤ) : (completion_of_ratfunc K) → K := sorry -- use `eval_fae` and `unif_cnts_fae` to prove that the first extends to the completion

lemma cauchy_fae (d : ℤ) (α : filter (completion_of_ratfunc K)) (hα : cauchy α) :
  cauchy (α.map (eval_compl_fae K d)) := sorry

variables (d : ℤ) (ℱ : filter (completion_of_ratfunc K))
#check ℱ.map (eval_compl_fae K d) --questo tizio è di Cauchy ma K è banale, quindi è costante!

def isom : 
  -- adic_completion.field (ratfunc K) (ideal_X K) ≃ ℤ := sorry
  (completion_of_ratfunc K) ≃ (laurent_series K) :=
{ to_fun :=
  begin
  intro α,
  apply hahn_series.mk,
  swap,
  intro d,
  obtain ⟨ℱ, hℱ⟩ := (quot.exists_rep α).some,
  have hℱ1 := cauchy_iff.mp hℱ,
  have hℱ2 := hℱ.2,
  have hℱ_unif := hℱ.2 (set_fae K d) (entourage_fae K d),
  let T := hℱ_unif.some,
  have hT := hℱ_unif.some_spec,
  have hT_nebot : T.nonempty,
  sorry,
  have : true,
  obtain ⟨x, hx⟩ := set.nonempty_def.mp hT_nebot,
  -- let x := hT_nebot.some,
  -- have hx := ht_nebot.some_mem,
  -- rcases hT with ⟨a, b⟩,
  -- let φ : 
  -- apply hahn_series.mk,
  -- swap,
  -- use λ n, Lim k (ss_int K α k).coeff n,

  obtain ⟨a, ha⟩ := (quot.exists_rep α).some,
  let b := a.map (ratfunc.coe_alg_hom K),
  let φ : ℤ → (laurent_series K → K) := λ i : ℤ, λ F : (laurent_series K), F.coeff i,
  apply hahn_series.mk,
  swap,
  intro d,
  let c:= b.map (φ d),
  letI : topological_space K := sorry,--discrete one
  use Lim c,
  -- have hc : cauchy c, sorry,
  -- have : ∃ (t : set (laurent_series K)), t ∈ b ∧ nonempty t ∧ (∀ F G : (laurent_series K), F ∈ t → G ∈ t → F.coeff d = G.coeff d),
  -- sorry,
  -- let F : laurent_series K := ((this.some_spec).2.1).some,
  -- use F.coeff d,
  -- sorry,

  end,
  inv_fun := sorry,
  left_inv := sorry,
  right_inv := sorry }

