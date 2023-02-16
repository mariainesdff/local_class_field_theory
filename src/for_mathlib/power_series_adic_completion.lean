/-
Copyright (c) 2022 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import for_mathlib.num_denom_away
import ring_theory.dedekind_domain.adic_valuation
import ring_theory.laurent_series
import ring_theory.power_series.well_known

open polynomial is_dedekind_domain.height_one_spectrum topological_space ratfunc sequentially_complete filter
open_locale big_operators discrete_valuation uniformity filter topology

-- open filter topological_space set classical uniform_space function
-- open_locale classical uniformity topological_space filter

section for_mathlib
open power_series laurent_series hahn_series multiplicative is_dedekind_domain

variables {F : Type*} [field F] (f g : ratfunc F)

@[simp, norm_cast] lemma coe_sub : ((f - g : ratfunc F) : laurent_series F) = f - g :=
(coe_alg_hom F).map_sub _ _

-- variables {R : Type*} [comm_ring R] [is_domain R] [is_dedekind_domain R] {K : Type*} [field K]
--   [algebra R K] [is_fraction_ring R K] (v : height_one_spectrum R)

-- open is_dedekind_domain.height_one_spectrum

-- lemma valuation_le_pow_iff_dvd (x : K) (n : ℤ) :
--   v.valuation x ≤ multiplicative.of_add (- n ) ↔ v.as_ideal^n ∣ ideal.span {x} :=

end for_mathlib


variables (K : Type*) [field K]

noncomputable theory

def ideal_X : is_dedekind_domain.height_one_spectrum (polynomial K) := 
{ as_ideal := ideal.span({X}),
  is_prime := by { rw ideal.span_singleton_prime, exacts [prime_X, X_ne_zero] },
  ne_bot   := by { rw [ne.def, ideal.span_singleton_eq_bot], exact X_ne_zero }} 

@[simp]
lemma ideal_X_span : (ideal_X K).as_ideal = ideal.span({polynomial.X}) := rfl

lemma val_X_eq_one : (ideal_X K).valuation (X : ratfunc K) = multiplicative.of_add (-1 : ℤ) := 
sorry

def completion_of_ratfunc  := adic_completion (ratfunc K) (ideal_X K)

instance : field (completion_of_ratfunc K) := adic_completion.field (ratfunc K) (ideal_X K)

instance : algebra K (polynomial K) := infer_instance

instance : uniform_space (ratfunc K) :=
  (@adic_valued (polynomial K) _ _ _ (ratfunc K) _ _ _ (ideal_X K)).to_uniform_space

instance : valued (completion_of_ratfunc K) ℤₘ₀ :=
  @valued.valued_completion _ _ _ _ (ideal_X K).adic_valued

instance : uniform_space (completion_of_ratfunc K) := 
begin
  apply_instance,
end
  -- is_dedekind_domain.height_one_spectrum.uniform_space_adic_completion (ratfunc K) _

-- lemma foo : (nhds (0 : ratfunc K)).has_basis set.univ (λ n : ℕ,
--   {F : (ratfunc K) | ↑(multiplicative.of_add (n : ℤ)) ≤ (ideal_X K).valuation F}) :=
-- begin
--   sorry
-- end

-- lemma foo' : (nhds (0 : ratfunc K)).has_basis set.univ (λ n : ℤ,
--   {F : (ratfunc K) | ↑(multiplicative.of_add n) ≤ (ideal_X K).valuation F}) :=
-- begin
--   sorry
-- end

-- def boo := filter.has_basis.uniformity_of_nhds_zero (foo K)

-- #check boo K

-- lemma boo_subset (n : ℕ) : (boo K n) ∈ (𝓤 (ratfunc K)) :=
-- variable (d : ℤ)
-- #check foo K

-- lemma uff : true := sorry
-- include K F

-- def ss (F : completion_of_ratfunc K) : ℕ → (ratfunc K) := seq ((quot.exists_rep F).some).2
--     (λ n, @filter.has_basis.mem_of_mem _ _ _ _ _ n
--     (filter.has_basis.uniformity_of_nhds_zero (foo K)) trivial)

variable (F : completion_of_ratfunc K)
#check filter.map (ratfunc.coe_alg_hom K) ((quot.exists_rep F).some).1



-- #check ss K F
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

-- def ss_int : ℤ → laurent_series K
-- |(n : nat) := ss K F n
-- | _ := 0

-- lemma foo2 (α : Type*) (u : ℕ → α) (N : ℕ) (hu : ∀ m : ℕ, N ≤ m → u m = u N) :
--   at_top.map u ≤ pure (u N) := --at_top.map u ≤ 𝓟 ({u N}) :=
-- begin
--   simp only [le_pure_iff, mem_map, mem_at_top_sets, ge_iff_le, set.mem_preimage,
--     set.mem_singleton_iff],
--   exact ⟨N, hu⟩,
-- end

-- lemma bar (α : Type*) (u : ℕ → α) (N : ℕ) (H : at_top.map u ≤ pure (u N)) :
--   ∃ d, ∀ m : ℕ, d ≤ m → u m = u d :=
--   --  := --at_top.map u ≤ 𝓟 ({u N}) :=
-- begin
--   -- intros m hm,
--   -- simp only [le_pure_iff, mem_map, mem_at_top_sets, ge_iff_le, set.mem_preimage,
--   --   set.mem_singleton_iff] at H,
--   simp at H,
--   obtain ⟨a, ha⟩ := H,
--   use a,
--   intros m hm,
--   by_cases a ≤ N,
--   { have : u a = u N,
--     exact ha a (le_of_eq (refl _)),
--     rw this,
--     exact ha _ hm },
--   { replace h : N < a, sorry, sorry,  },
--   -- let A := min a N,
--   -- have hm' : A ≤ m,
--   -- simp * at *,
--   -- apply ha,
--   -- have := (le_of_eq (refl a)),
--   -- specialize ha b (le_max_iff.mpr _),
--   -- apply or.intro_left _, 
--   -- exact this,
  
--   -- simp only [this, true_or],
--   -- have := (true_or (le_of_eq (refl a))),

--   -- squeeze_simp [b],
--   -- simp only [le_pure_iff, mem_map, mem_at_top_sets, ge_iff_le, set.mem_preimage,
--   --   set.mem_singleton_iff],
--   -- exact ⟨N, hu⟩,
-- end

-- def eventual_coeff (ℱ : filter (ratfunc K)) (h : cauchy ℱ) (d : ℤ) : K :=
-- -- ∃ (t : set (laurent_series K)), t ∈ ℱ.map (ratfunc.coe_alg_hom K) ∧ t ≠ ∅ ∧ (∀ F G : (laurent_series K), F ∈ t → G ∈ t → F.coeff d = G.coeff d),
--   sorry

-- def temp_coeff : ℤ → (laurent_series K → K) := λ i F, F.coeff i

-- lemma eventually_eq_eventual_coeff (ℱ : filter (ratfunc K)) (h : cauchy ℱ) (d : ℤ) :
--   -- ( T : set (completion_of_ratfunc K)) : 
--   ∀ T ∈ ℱ, (ℱ.map (ratfunc.coe_alg_hom K)).map (temp_coeff K d) = (ℱ.map (ratfunc.coe_alg_hom K)).map (temp_coeff K d) :=
-- begin
--   sorry,
-- end

-- example (X : Type*) [uniform_space X] (ℱ : filter X) (hF : cauchy ℱ) :
--   ∃ x : uniform_space.completion X, ℱ.map coe ≤ 𝓝 x :=
-- begin
--   refine complete_space.complete _,
--   refine cauchy.map hF _,
--   refine uniform_space.completion.uniform_continuous_coe X,
-- end


def set_fae (d : ℤ) : set (ratfunc K × ratfunc K) :=
  {P | (ideal_X K).valuation (P.1 - P.2) < ↑(multiplicative.of_add (- d))}

-- *FAE* This was the old definition, but I think I got the inequalities wrong, since I did not
-- know yet how to play with `multiplicative.of_add`.
-- def set_fae (d : ℤ) : set (ratfunc K × ratfunc K) :=
--   {P | ↑(multiplicative.of_add d) ≤ (ideal_X K).valuation (P.1 - P.2)}

lemma fae_for_pol (f  : polynomial K) (d : ℕ) (hf : (ideal_X K).int_valuation f ≤ 
  ↑(multiplicative.of_add (- (d+(1 : ℕ)) : ℤ))) : f.coeff d = 0 :=
begin 
  erw [int_valuation_le_pow_iff_dvd _ _ (d+1)] at hf,
  simp only [ideal_X_span, ideal.dvd_span_singleton, ideal.span_singleton_pow,
    ideal.mem_span_singleton'] at hf,
  cases hf with a ha,
  simp only [← ha, coeff_mul_X_pow', add_le_iff_nonpos_right, le_zero_iff, nat.one_ne_zero,
    if_false],
end


-- lemma fae_pol (f : ratfunc K)  (d : ℤ) (hf : (ideal_X K).valuation f ≤
--   ↑(multiplicative.of_add (- d - 1))) : 
--   ratfunc.X^d * f  ∈ (algebra_map (polynomial K) (ratfunc K)).range :=
-- begin
--   suffices : (ideal_X K).valuation (ratfunc.X^d * f) ≤ ↑(multiplicative.of_add (- d - 1)),

-- end

instance : is_principal_ideal_ring (power_series K) := sorry

variable [decidable_eq (power_series K)]
lemma boo : unique_factorization_monoid (power_series K):=
begin
  -- haveI : is_principal_ideal_ring (power_series K), sorry,
  apply principal_ideal_ring.to_unique_factorization_monoid,
end

variable [unique_factorization_monoid (power_series K)]
variable [decidable_rel (has_dvd.dvd : (power_series K) → (power_series K) → Prop)]
variable [normalization_monoid (power_series K)]

def unit_X : (laurent_series K)ˣ :=
  @self_as_unit (power_series K) _ _ _ _ _ _ (power_series.X) (laurent_series K) _ _ _

lemma fae_denom_X (f : ratfunc K) (hf : f ≠ 0) : 
  ∃ (g : power_series K) (n : ℤ), ¬ power_series.X ∣ g ∧
  (((unit_X K)^n * g) : laurent_series K)= f :=
begin
  obtain ⟨g, n, hg, hn⟩ := exists_reduced_fraction _ (laurent_series K)
    (@prime.irreducible (power_series K) _ _ (power_series.X_prime)) f _,
  have : is_localization.mk' (laurent_series K) g 1 = g := is_localization.mk'_one _ _,
  use [g, n, hg],
  { rw ← this,
    convert hn,
    rw units.coe_zpow,
    refl },
  { rw [← ratfunc.coe_zero],
    exact ratfunc.coe_injective.ne hf},
end

open laurent_series

lemma val_X_fae : ((X : ratfunc K): laurent_series K).order = 1 :=
by simp only [ratfunc.coe_X, hahn_series.order_single, ne.def, one_ne_zero, not_false_iff]

example (f : laurent_series K) (hf : f ≠ 0) : (hahn_series.add_val ℤ K f) = f.order :=
begin
  exact hahn_series.add_val_apply_of_ne hf,
end

lemma fae_X_pow (n : ℕ) : (hahn_series.single (n : ℤ) 1) =
  ((X :ratfunc K) : laurent_series K) ^ n :=
begin
induction n with n h_ind ,
    { simp only [nat.nat_zero_eq_zero, int.of_nat_eq_coe, zmod.nat_cast_self, zpow_zero],
     refl, },
    { rw ← int.coe_nat_add_one_out,
      rw [← one_mul (1 : K)],
      rw ← hahn_series.single_mul_single,
      rw h_ind,
      rw ratfunc.coe_X,
      rw pow_succ' },
end

lemma fae_single_inv (d : ℤ) (α : K) (hα : α ≠ 0) : (hahn_series.single (d : ℤ) (α : K))⁻¹ 
  = hahn_series.single (-d) (α⁻¹ : K) :=
by {rw [inv_eq_of_mul_eq_one_left], simpa only [hahn_series.single_mul_single, 
  add_left_neg, inv_mul_cancel hα]}


lemma fae_X_zpow (n : ℤ) : (hahn_series.single (n : ℤ) 1) =
  ((X :ratfunc K) : laurent_series K) ^ n :=
begin
  induction n with n_pos n_neg,
  apply fae_X_pow,
  rw ratfunc.coe_X,
  have := fae_single_inv K ((n_neg + 1) : ℤ) 1 one_ne_zero,
  rw int.neg_succ_of_nat_coe,
  rw int.coe_nat_add,
  rw nat.cast_one,
  nth_rewrite 0 [← inv_one],
  rw ← this,
  rw zpow_neg,
  rw ← nat.cast_one,
  rw ← int.coe_nat_add,
  rw fae_X_pow,
  rw ratfunc.coe_X,
  rw [algebra_map.coe_one, inv_inj],
  rw zpow_coe_nat,
end



lemma fae_order_eq_val (f : ratfunc K) (hf : f ≠ 0) :
 ↑(multiplicative.of_add (- (f : laurent_series K).order)) = ((ideal_X K).valuation f) :=
begin
  set F : laurent_series K := f with hF,
  set m := F.order with hm,
  set A := power_series_part F with hA,
  set a := ratfunc.X ^(-m) * f with ha,
  have haA : (a : laurent_series K) = A,
  { have uno := of_power_series_power_series_part F,
    rw hA,
    rw ha,
    rw ← hm at uno,
    rw fae_X_zpow at uno,
    rw hF at uno,
    rw ratfunc.coe_mul,
    simp only [ratfunc.coe_def, map_zpow₀],
    exact uno.symm, },
    replace ha : ratfunc.X^m * a = f,
    {rwa [zpow_neg, eq_inv_mul_iff_mul_eq₀] at ha,
      exact (zpow_ne_zero _ ratfunc.X_ne_zero)},
    rw ← ha,
    rw valuation.map_mul,
    rw map_zpow₀,
    rw val_X_eq_one,
    have : (ideal_X K).valuation a = 1,
    sorry,
    rw this,
    rw [mul_one, ← with_zero.coe_zpow, ← of_add_zsmul, smul_neg, zsmul_one],
    refl,
end


-- do for general hahn series
lemma fae_order_neg {f : ratfunc K} : -- (hf : f ≠ 0) :
 (- f : laurent_series K).order = (f : laurent_series K).order :=
begin
  classical,
  by_cases hf : f = 0,
  { simp only [hf, ratfunc.coe_zero, neg_zero]},
  { simp only [hahn_series.order, hahn_series.support_neg, neg_eq_zero]}
end

lemma fae_order_eq_val' (f : ratfunc K) (hf : f ≠ 0) :
 ↑(multiplicative.of_add ((f : laurent_series K).order)) = ((ideal_X K).valuation f)⁻¹ :=
begin
  have := fae_order_eq_val K (-f) (neg_ne_zero.mpr hf),
  nth_rewrite 0 [← neg_neg f],
  rw ratfunc.coe_def,
  rw (ratfunc.coe_alg_hom K).map_neg,
  rw ← ratfunc.coe_def,
  rw fae_order_neg,
  rw of_add_neg at this,
  rw [← with_zero.coe_unzero $((ideal_X K).valuation).ne_zero_iff.mpr hf],
  rw ← with_zero.coe_inv,
  rw with_zero.coe_inj,
  rw eq_inv_iff_eq_inv,
  rw ← with_zero.coe_inj,
  simp only [this, with_zero.coe_unzero, valuation.map_neg],
end

lemma coeff_fae (d : ℤ) (x y : ratfunc K) (H : (x, y) ∈ (set_fae K d)) :
 (x : laurent_series K).coeff d = (y : laurent_series K).coeff d :=
begin
  by_cases triv : x = y,
  { rw triv },
  { dsimp only [set_fae] at H,
    apply eq_of_sub_eq_zero,
    rw [← hahn_series.sub_coeff],
    rw [← coe_sub],
    apply hahn_series.coeff_eq_zero_of_lt_order,
    rw ← multiplicative.of_add_lt,
    rw ← with_zero.coe_lt_coe,
    rw @fae_order_eq_val' K _ _ _ _ _ (x - y) (sub_ne_zero_of_ne triv),
    rw [of_add_neg] at H,
    replace triv : ((ideal_X K).valuation) (x - y) ≠ 0 :=
      (valuation.ne_zero_iff _).mpr (sub_ne_zero_of_ne triv),
    rw ← with_zero.coe_unzero triv,
    rw ← with_zero.coe_inv,
    rw with_zero.coe_lt_coe,
    rw lt_inv',
    rw ← with_zero.coe_lt_coe,
    rw with_zero.coe_unzero triv,
    exact H },
end



lemma entourage_fae (d : ℤ) : set_fae K d ∈ 𝓤 (ratfunc K) :=
begin
  sorry,
end

-- instance discrete_fae : uniform_space K := ⊤

def eval_fae (d : ℤ) : ratfunc K → K := λ x : ratfunc K, (x : laurent_series K).coeff d

lemma unif_cnts_fae (d : ℤ) {uK : uniform_space K} (h : uniformity K = 𝓟 id_rel)
: uniform_continuous (eval_fae K d) :=
begin
  refine uniform_continuous_iff_eventually.mpr _,
  intros S hS,
  rw h at hS,
  simp only [mem_principal, id_rel_subset] at hS,--probably useless,
  refine eventually_iff_exists_mem.mpr _,
  use set_fae K d,
  split,
  exact entourage_fae K d,
  intros x hx,
  suffices : (eval_fae K d x.fst) = (eval_fae K d x.snd),
  rw this,
  exact (hS (eval_fae K d x.snd)),
  apply coeff_fae,
  exact hx,
end

-- lemma discrete_complete_fae (d : ℤ) {uK : uniform_space K}
--   (h : uniformity K = 𝓟 id_rel) : is_complete (⊤ : (set K)) :=
-- begin
--   sorry
-- end

-- def eval_compl_fae (d : ℤ) {uK : uniform_space K}
--   (h : uniformity K = 𝓟 id_rel) : (completion_of_ratfunc K) → K := 
--   uniform_space.completion.extension (eval_fae K d)

--the `instance : uniform_space (completion_of_ratfunc K) :=` is needed for the `lemma` below
lemma cauchy_fae (d : ℤ) {uK : uniform_space K} (h : uniformity K = 𝓟 id_rel)
  (α : filter (ratfunc K)) (hα : cauchy α) :
  cauchy (α.map (eval_fae K d)) := hα.map (unif_cnts_fae K d h)


def constant_cauchy_fae {uK : uniform_space K} (h : uniformity K = 𝓟 id_rel) 
  (α : filter K) (hα : cauchy α) : K :=
begin
  sorry
end

lemma constant_cauchy_fae_principal {uK : uniform_space K} 
  (h : uniformity K = 𝓟 id_rel) (α : filter K) (hα : cauchy α) :
  α ≤ filter.principal {constant_cauchy_fae K h α hα} := sorry


def isom 
  {uK : uniform_space K} (h : uniformity K = 𝓟 id_rel) : 
  -- adic_completion.field (ratfunc K) (ideal_X K) ≃ ℤ := sorry
  (completion_of_ratfunc K) ≃ (laurent_series K) :=
{ to_fun :=
  begin
  intro α,
  apply hahn_series.mk,
  swap,
  intro d,
  obtain ⟨ℱ, hℱ⟩ := (quot.exists_rep α).some,
  use (constant_cauchy_fae K h (ℱ.map (eval_fae K d)) (cauchy_fae K d h ℱ hℱ)),
  have : set.is_pwo (⊤ : (set ℤ)),
  sorry,
  exact set.is_pwo.mono this (set.subset_univ _),
  end,
  inv_fun := sorry,
  left_inv := sorry,
  right_inv := sorry }

