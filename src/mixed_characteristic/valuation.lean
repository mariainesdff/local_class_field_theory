/-
Copyright (c) 2022 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import data.polynomial.eval
import number_theory.padics.padic_integers
import ring_theory.dedekind_domain.adic_valuation
import ring_theory.polynomial.basic
import mixed_characteristic.basic
import for_mathlib.spectral_norm

noncomputable theory

-- /- 
-- * Topology on K + this is locally compact.
-- * Define normalized discrete valuation on K, using topological nilpotent elements.
-- * Unit ball = ring of integers
-- * Top. nilp. elements are a maximal ideal P in O_K
-- * Define ramification index e
-- * P^e = (p)
-- * Relate to norm (future)
-- -/

lemma foo (R S K L : Type*) 
  [comm_ring R] 
  -- [cancel_comm_monoid_with_zero Z]
  [is_domain R]
  [normalized_gcd_monoid R]
  [field K]
  [comm_ring S] 
  [is_domain S]
  [comm_ring L]
  [nontrivial L]
  [algebra R S]
  [algebra R K] 
  [algebra S L] 
  [algebra R L]
  [algebra K L]
  [is_fraction_ring R K]
  [is_fraction_ring S L]
  [is_scalar_tower R S L]
  [is_scalar_tower R K L]
  (x : S)
   (hx : is_integral R x) :
    polynomial.map (algebra_map R K) (minpoly R x) = minpoly K (algebra_map S L x) :=
  begin
  haveI obvious : no_zero_smul_divisors S L, sorry,
  have h_Z_monic := minpoly.monic hx,
  have h_Q_monic := polynomial.monic.map (algebra_map R K) h_Z_monic,
  refine minpoly.eq_of_irreducible_of_monic _ _ h_Q_monic,
  apply (polynomial.is_primitive.irreducible_iff_irreducible_map_fraction_map 
    h_Z_monic.is_primitive).mp,
      { exact minpoly.irreducible hx },
      {apply_instance},
    { erw [polynomial.aeval_map_algebra_map K (algebra_map S L x) _],
      exact (polynomial.aeval_algebra_map_eq_zero_iff L x _).mpr (minpoly.aeval _ _),
      apply_instance },
  end

open is_dedekind_domain nnreal polynomial

open_locale mixed_char_local_field nnreal

variables {p : ℕ} [fact (p.prime)] 
variables {K: Type*} [field K] [mixed_char_local_field p K]

def norm_on_K : K → ℝ := spectral_norm (algebra.is_algebraic_of_finite ℚ_[p] K)

variables (p K)

lemma norm_of_int_le_one (x : 𝓞 p K) : norm_on_K (x : K) ≤ 1 :=
begin
  let min_Z := minpoly ℤ_[p] x,
  have h_Z_monic := minpoly.monic (is_integral_closure.is_integral ℤ_[p] K x),
  let min_Q : polynomial ℚ_[p] := polynomial.map padic_int.coe.ring_hom min_Z,
  have h_Q_monic : monic min_Q := polynomial.monic.map padic_int.coe.ring_hom h_Z_monic,
  have is_minpoly : min_Q = @minpoly ℚ_[p] K _ _ _ (x : K), sorry,
  -- { refine minpoly.eq_of_irreducible_of_monic _ _ h_Q_monic,
  --   { haveI : normalized_gcd_monoid ℤ_[p], sorry,
  --     apply (is_primitive.irreducible_iff_irreducible_map_fraction_map h_Z_monic.is_primitive).mp,
  --     { exact minpoly.irreducible(is_integral_closure.is_integral ℤ_[p] K x) },
  --     { apply_instance }},
  --   { erw [polynomial.aeval_map_algebra_map ℚ_[p] (x : K) min_Z],
  --     exact (polynomial.aeval_algebra_map_eq_zero_iff K x min_Z).mpr (minpoly.aeval _ _) }},
  have : norm_on_K (x : K) = spectral_value h_Q_monic,
  simp only [norm_on_K, spectral_norm, ← is_minpoly],
  rw [this],
  refine csupr_le _,
  intro n,
  simp only [spectral_value_terms],
  split_ifs with hn,
  { have coeff_coe : ∀ n : ℕ, min_Q.coeff n = min_Z.coeff n :=
    λ n, by {simpa only [polynomial.coeff_map]},
    rw [coeff_coe n, padic_int.padic_norm_e_of_padic_int],
    apply real.rpow_le_one (norm_nonneg _) (polynomial.coeff min_Z n).norm_le_one,
    simp only [one_div, inv_nonneg, sub_nonneg, nat.cast_le],
    exact (le_of_lt hn) },
  { exact zero_le_one },
end

def open_unit_ball : height_one_spectrum (𝓞 p K) :=
{ as_ideal := 
  { carrier   := { x : 𝓞 p K | norm_on_K (x : K) < 1},
    add_mem'  := λ x y hx hy,
    begin
      rw [set.mem_set_of_eq, norm_on_K] at hx hy ⊢,
      exact lt_of_le_of_lt (spectral_norm.is_nonarchimedean _ padic_norm_e.nonarchimedean (x : K)
        (y : K)) (max_lt_iff.mpr ⟨hx, hy⟩),
    end,  
    zero_mem' := 
    begin
      rw [set.mem_set_of_eq, zero_mem_class.coe_zero, norm_on_K, spectral_norm_zero _],
      exact zero_lt_one,
    end,
    smul_mem' := λ k x hx,
    begin
      dsimp only [norm_on_K],
      rw smul_eq_mul,
      have := spectral_norm.mul (algebra.is_algebraic_of_finite ℚ_[p] K) (k : K) (x : K)
        padic_norm_e.nonarchimedean,
      convert_to spectral_norm (algebra.is_algebraic_of_finite ℚ_[p] K) ((k : K) * (x : K)) < 1,
      rw this,
      exact mul_lt_one_of_nonneg_of_lt_one_right (norm_of_int_le_one p K k)
        (spectral_norm_nonneg _ _) hx,
    end },
  is_prime := 
  begin
    rw ideal.is_prime_iff,
    split,
    { rw ideal.ne_top_iff_one,
      simp only [set.mem_set_of_eq, submodule.mem_mk, one_mem_class.coe_one, not_lt],
      sorry },
    { intros x y hxy,
      simp only [set.mem_set_of_eq, submodule.mem_mk, mul_mem_class.coe_mul] at hxy ⊢,
      sorry }
  end,
  ne_bot   := --TODO: golf
  begin
    apply ne_of_gt,
    --apply lt_of_le_not_le,
    split,
    { --exact bot_le, 
      simp only [submodule.bot_coe, submodule.coe_set_mk, set.singleton_subset_iff,
        set.mem_set_of_eq, zero_mem_class.coe_zero, norm_on_K, spectral_norm_zero _],
      exact zero_lt_one, },
    { simp only [submodule.coe_set_mk, submodule.bot_coe, set.subset_singleton_iff,
        set.mem_set_of_eq, not_forall, exists_prop], 
      refine ⟨(p : 𝓞 p K), _, ne_zero.ne ↑p⟩,
       --TODO : some coercions are needed, but it should work.
      have : ((p : 𝓞 p K) : K) = algebra_map ℚ_[p] K (p : ℚ_[p]) :=
        by {simp only [subring_class.coe_nat_cast, map_nat_cast]},
      rw [norm_on_K, this, spectral_norm.extends (algebra.is_algebraic_of_finite ℚ_[p] K) p],
      exact padic_norm_e.norm_p_lt_one }
  end }

def normalized_valuation : valuation K (with_zero (multiplicative ℤ)) :=
(open_unit_ball p K).valuation

-- section add_comm_monoid

-- variables {R : Type*} (Rₛ : Type*) [comm_ring R] [comm_ring Rₛ] [algebra R Rₛ]
-- variables (S : submonoid R) [hT : is_localization S Rₛ]

-- include hT

-- variables {M N : Type*} [add_comm_monoid M] [add_comm_monoid N] [module R M] [module R N]
-- variables [module Rₛ M] [is_scalar_tower R Rₛ M] [module Rₛ N] [is_scalar_tower R Rₛ N]

-- -- def linear_map.localization (f : M →ₗ[R] N) : 

-- end add_comm_monoid

-- set_option profiler true
--namespace mixed_char_local_field

/- section non_standard_topology

open_locale mixed_char_local_field


variables (p : ℕ) [fact (p.prime)] 
variables (K: Type*) [field K] [mixed_char_local_field p K]

def pi_equiv_int : (fin (finite_dimensional.finrank ℤ_[p] (𝓞 p K)) → ℤ_[p]) ≃ₗ[ℤ_[p]] 𝓞 p K := 
begin
  sorry,
  -- have := @finite_dimensional.linear_equiv.of_finrank_eq (𝓞 p K)
  --   (fin (finite_dimensional.finrank ℤ_[p] (𝓞 p K)) → ℤ_[p]),
  -- -- simp only [finite_dimensional.finrank_fin_fun],
  -- -- exacts [mixed_char_local_field.to_finite_dimensional,
  -- --   finite_dimensional.finite_dimensional_pi ℚ_[p]],
end

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

lemma mixed_char_local_field.to_t2_space : @t2_space K (mixed_char_local_field.pi_topology p K):=
begin
  letI := mixed_char_local_field.pi_topology p K,
  exact homeomorph.t2_space (pi_homeo p K).symm,
end

end non_standard_topology -/

/- section open_unit_ball

open mixed_char_local_field
open_locale mixed_char_local_field

variables {p : ℕ} [fact (p.prime)] 
variables {K: Type*} [field K] [mixed_char_local_field p K]

lemma ring_of_integers.to_t2_space : 
  @t2_space (𝓞 p K) (@subtype.topological_space K _
  (mixed_char_local_field.pi_topology p K)) := @subtype.t2_space K _
    (mixed_char_local_field.pi_topology p K) (to_t2_space p K)

def is_topologically_nilpotent (x : 𝓞 p K) : Prop :=
  filter.tendsto (λ n : ℕ, x^n) filter.at_top (@nhds (𝓞 p K) (@subtype.topological_space K
  (λ x, is_integral ℤ_[p] x) (mixed_char_local_field.pi_topology p K)) 0)

variable (K)

-- `FAE` : This lemma is certainly false
lemma is_topologically_nilpotent_iff_forall_i (x : 𝓞 p K) : is_topologically_nilpotent x ↔
  ∀ i : (fin (finite_dimensional.finrank ℚ_[p] K)), ∥ ((pi_equiv p K) x i) ∥ < 1 :=
begin
  sorry,
end

lemma is_topological_nilpotent_add (x y : 𝓞 p K) (hx : is_topologically_nilpotent x)
  (hy : is_topologically_nilpotent y) : is_topologically_nilpotent (x + y) :=
begin
  rw is_topologically_nilpotent_iff_forall_i at hx hy ⊢,
  intro i,
  simp only [add_mem_class.coe_add, map_add, pi.add_apply],
  apply lt_of_le_of_lt (padic_norm_e.nonarchimedean _ _),
  exact max_lt_iff.mpr ⟨hx i, hy i⟩,
end

#exit

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

end open_unit_ball -/