/-
Copyright (c) 2022 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

/- import data.polynomial.eval
import data.real.nnreal
import number_theory.padics.padic_integers
import ring_theory.dedekind_domain.adic_valuation
import ring_theory.polynomial.basic -/
import eq_characteristic.basic
import from_mathlib.normed_valued
import from_mathlib.spectral_norm_unique

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

open is_dedekind_domain nnreal polynomial ratfunc
open_locale eq_char_local_field nnreal discrete_valuation

variables {p : ℕ} [fact (p.prime)] 


namespace FpX_field_completion

noncomputable! instance : is_rank_one (@FpX_field_completion.with_zero.valued p _).v :=
{ hom         := sorry,
  strict_mono := sorry,
  nontrivial  := begin
    use algebra_map (ratfunc 𝔽_[p]) 𝔽_[p]⟮⟮X⟯⟯ X,
    rw FpX_field_completion.valuation_X, -- wrong namespace (fix in basic file)
    split,
    { exact with_zero.coe_ne_zero,},
    { rw [← with_zero.coe_one, ne.def, with_zero.coe_inj, of_add_eq_one, neg_eq_zero],
      exact one_ne_zero }
  end }

instance : normed_field 𝔽_[p]⟮⟮X⟯⟯ := rank_one_valuation.valued_field.to_normed_field

end FpX_field_completion

namespace FpX_int_completion
--`[FAE]` The following `instance` will probably be PR'd soon in greater generality for all
-- integrally closed domains: see 
-- [https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/.E2.9C.94.20gcd_monoid]
noncomputable! instance  : normalized_gcd_monoid 𝔽_[p]⟦X⟧  :=
sorry

end FpX_int_completion

variables {K : Type*} [field K] [eq_char_local_field p K]

namespace eq_char_local_field

def norm_on_K : K → ℝ := spectral_norm 𝔽_[p]⟮⟮X⟯⟯ K

def nnnorm_on_K [eq_char_local_field p K] : K → ℝ≥0 :=
λ x, ⟨norm_on_K x, spectral_norm_nonneg x⟩

@[simp] lemma coe_nnnorm {K : Type*} [field K] [eq_char_local_field p K] (x : K) : 
  ((nnnorm_on_K x) : ℝ) = norm_on_K x :=
rfl

@[ext] lemma nnnorm_ext_norm {K : Type*} [field K] [eq_char_local_field p K] (x y : K) : 
  (nnnorm_on_K x) = (nnnorm_on_K y) ↔ norm_on_K x = norm_on_K y :=
subtype.ext_iff

--same proof as in mixed char case
lemma norm_on_K_one {K : Type*} [field K] [eq_char_local_field p K] : norm_on_K (1 : K) = 1 := 
by rw [norm_on_K, spectral_norm_is_norm_one_class]

lemma norm_of_int_le_one (x : 𝓞 p K) : norm_on_K (x : K) ≤ 1 :=
begin
  sorry
  /- let min_Z := minpoly ℤ_[p] x,
  have h_Z_monic := minpoly.monic (is_integral_closure.is_integral ℤ_[p] K x),
  let min_Q : polynomial ℚ_[p] := polynomial.map padic_int.coe.ring_hom min_Z,
  have h_Q_monic : monic min_Q := polynomial.monic.map padic_int.coe.ring_hom h_Z_monic,
  have is_minpoly : min_Q = @minpoly ℚ_[p] K _ _ _ (x : K),
  exact (minpoly.is_integrally_closed_eq_field_fractions ℚ_[p] K (is_integral_closure.is_integral
    ℤ_[p] K x)).symm,
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
  { exact zero_le_one }, -/
end

variables (K)

noncomputable! def open_unit_ball : height_one_spectrum (𝓞 p K) :=
{ as_ideal := 
  { carrier   := { x : 𝓞 p K | norm_on_K (x : K) < 1},
    add_mem'  := λ x y hx hy,
    begin
      sorry
      /- rw [set.mem_set_of_eq, norm_on_K] at hx hy ⊢,
      refine lt_of_le_of_lt (spectral_norm_is_nonarchimedean 
        (algebra.is_algebraic_of_finite ℚ_[p] K) padic_norm_e.nonarchimedean (x : K)
        (y : K)) (max_lt_iff.mpr ⟨hx, hy⟩), -/
    end,  
    zero_mem' := 
    begin
      rw [set.mem_set_of_eq, zero_mem_class.coe_zero, norm_on_K, spectral_norm_zero],
      exact zero_lt_one,
    end,
    smul_mem' := λ k x hx,
    begin
      sorry/- rw [norm_on_K, smul_eq_mul, set.mem_set_of_eq, mul_mem_class.coe_mul,
        ← spectral_alg_norm_def (algebra.is_algebraic_of_finite ℚ_[p] K)
          padic_norm_e.nonarchimedean,
        spectral_norm_is_mul (algebra.is_algebraic_of_finite ℚ_[p] K)
          padic_norm_e.nonarchimedean (k : K) (x : K)],
      exact mul_lt_one_of_nonneg_of_lt_one_right (norm_of_int_le_one K k)
        (spectral_norm_nonneg _) hx, -/
    end },
  is_prime := 
  begin
    rw ideal.is_prime_iff,
    split,
    { rw ideal.ne_top_iff_one,
      simp only [set.mem_set_of_eq, submodule.mem_mk, one_mem_class.coe_one, not_lt],
      exact le_of_eq (norm_on_K_one).symm, },
    { sorry/- intros x y hxy,
      simp only [set.mem_set_of_eq, submodule.mem_mk, mul_mem_class.coe_mul] at hxy ⊢,
      rw [norm_on_K, ← spectral_alg_norm_def (algebra.is_algebraic_of_finite ℚ_[p] K) 
        padic_norm_e.nonarchimedean, spectral_norm_is_mul (algebra.is_algebraic_of_finite ℚ_[p] K) 
        padic_norm_e.nonarchimedean] at hxy, 
      contrapose! hxy,
      exact one_le_mul_of_one_le_of_one_le hxy.1 hxy.2, -/  }
  end,
  ne_bot   := --TODO: golf
  begin
    apply ne_of_gt,
    split,
    { simp only [submodule.bot_coe, submodule.coe_set_mk, set.singleton_subset_iff,
        set.mem_set_of_eq, zero_mem_class.coe_zero, norm_on_K, spectral_norm_zero],
      exact zero_lt_one, }, 
    { sorry/- simp only [submodule.coe_set_mk, submodule.bot_coe, set.subset_singleton_iff,
        set.mem_set_of_eq, not_forall, exists_prop], 
      refine ⟨(p : 𝓞 p K), _, ne_zero.ne ↑p⟩,
      have : ((p : 𝓞 p K) : K) = algebra_map ℚ_[p] K (p : ℚ_[p]) :=
        by {simp only [subring_class.coe_nat_cast, map_nat_cast]},
      rw [norm_on_K, this, spectral_norm_extends (p : ℚ_[p])],
      exact padic_norm_e.norm_p_lt_one -/ }
  end }

def normalized_valuation (K : Type*) [field K] [eq_char_local_field p K] : valuation K ℤₘ₀ :=
  (open_unit_ball K).valuation

instance (K : Type*) [field K] [eq_char_local_field p K] : valued K ℤₘ₀ :=
  valued.mk' (normalized_valuation K) 

instance : algebra (ratfunc 𝔽_[p]) K := algebra.comp (ratfunc 𝔽_[p]) 𝔽_[p]⟮⟮X⟯⟯ K

lemma normalized_valuation_X_ne_zero [eq_char_local_field p K] :
  (normalized_valuation K) (algebra_map (ratfunc 𝔽_[p]) _ X) ≠ 0 :=
by {simp only [ne.def, valuation.zero_iff, nat.cast_eq_zero], apply sorry/-  nat.prime.ne_zero (fact.out _) -/}  



open multiplicative is_dedekind_domain.height_one_spectrum
def ramification_index (K : Type*) [field K] [eq_char_local_field p K] : ℤ := 
  -(with_zero.unzero (normalized_valuation_X_ne_zero K)).to_add

localized "notation (name := ramification_index)
  `e` := eq_char_local_field.ramification_index" in eq_char_local_field 

end eq_char_local_field

namespace FpX_field_completion

open eq_char_local_field
variable (p)

-- Even compiling the statement is slow...
noncomputable! lemma open_unit_ball_def : 
  (open_unit_ball 𝔽_[p]⟮⟮X⟯⟯).as_ideal =
  ideal.span {(FpX_field_completion.ring_of_integers_equiv p).symm (FpX_int_completion.X p)} := 
begin
 sorry
  /- have hiff : ∀ (y : ℚ_[p]), y ∈ 𝓞 p ℚ_[p] ↔ ‖ y ‖  ≤ 1, -- we should extract this to a lemma
  { intro y, rw mem_ring_of_integers,
    rw is_integrally_closed.is_integral_iff,
    refine ⟨λ h, _, λ h, ⟨⟨y, h⟩, rfl⟩⟩,
    { obtain ⟨x, hx⟩ := h,
      rw [← hx],
      exact padic_int.norm_le_one _, }},
  simp only [open_unit_ball],
  ext ⟨x, hx⟩,
  have hx' : x = (⟨x, (hiff x).mp hx⟩ : ℤ_[p]) := rfl,
  rw [submodule.mem_mk, set.mem_set_of_eq, ideal.mem_span_singleton, norm_on_padic, 
    set_like.coe_mk],
  conv_lhs {rw hx'},
  rw [← padic_int.norm_def, padic_int.norm_lt_one_iff_dvd, dvd_iff_exists_eq_mul_left,
    dvd_iff_exists_eq_mul_left],
  refine ⟨λ h, _, λ h, _⟩,
  { obtain ⟨⟨c, hc⟩, hcx⟩ := h, 
    use ⟨c, (hiff c).mpr hc⟩,
    rw subtype.ext_iff at hcx ⊢,
    exact hcx },
  { obtain ⟨⟨c, hc⟩, hcx⟩ := h, 
    use ⟨c, (hiff c).mp hc⟩,
    rw subtype.ext_iff at hcx ⊢,
    exact hcx }, -/
end 

variable {p}

--set_option profiler true
/- lemma is_unramified_ℚ_p : e ℚ_[p] = 1 :=
begin
  have hp : normalized_valuation ℚ_[p] p = (of_add (-1 : ℤ)),
  { have hp0 : (p : 𝓞 p ℚ_[p]) ≠ 0,
    { simp only [ne.def, nat.cast_eq_zero], exact nat.prime.ne_zero (_inst_1.1) }, --looks bad
    have hp_alg : (p : ℚ_[p]) = algebra_map (𝓞 p ℚ_[p]) ℚ_[p] (p : 𝓞 p ℚ_[p]) := rfl,
    simp only [normalized_valuation],
    rw [hp_alg, valuation_of_algebra_map],
    simp only [int_valuation, ← valuation.to_fun_eq_coe],
    rw [int_valuation_def_if_neg _ hp0, ← padic.open_unit_ball_def, associates.count_self],
    refl,
    { exact associates_irreducible (open_unit_ball ℚ_[p]), }}, -- so slow!
  rw [ramification_index, neg_eq_iff_neg_eq, ← to_add_of_add (-1 : ℤ)],
  apply congr_arg,
  rw [← with_zero.coe_inj, ← hp, with_zero.coe_unzero],
 
end
 -/

end FpX_field_completion