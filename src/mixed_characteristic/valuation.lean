/-
Copyright (c) 2023 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import for_mathlib.padic_compare
import mixed_characteristic.basic
import from_mathlib.normed_valued

open discrete_valuation is_dedekind_domain multiplicative nnreal polynomial ratfunc 
open_locale mixed_char_local_field nnreal discrete_valuation

namespace mixed_char_local_field

variables (p : out_param (ℕ)) [hp : fact (p.prime)] 

include hp
variables (K : Type*) [field K] [mixed_char_local_field p K]

-- NOTE: There is a diamond on 𝔽_[p]⟮⟮X⟯⟯, but by setting this priority lower, it seems
-- that Lean finds the correct instance.
@[priority 100] instance : valued K ℤₘ₀ :=
extension.valued 𝔽_[p]⟮⟮X⟯⟯ K

#exit


def norm_on_K : K → ℝ := spectral_norm ℚ_[p] K

-- This causes a diamond with the p-adic norm on ℚ_p
/- instance : normed_field K := spectral_norm_to_normed_field (algebra.is_algebraic_of_finite ℚ_[p] K)
  padic_norm_e.nonarchimedean  -/

lemma norm_on_padic : ((norm_on_K ) : ℚ_[p] → ℝ) = (norm : ℚ_[p] → ℝ) := 
by { ext x, exact spectral_norm_extends _ }

def nnnorm_on_K : K → ℝ≥0 :=
λ x, ⟨@norm_on_K p _ K _ _ x, spectral_norm_nonneg x⟩

@[simp]
lemma coe_nnnorm {K : Type*} [field K] [mixed_char_local_field p K] 
  (x : K) : 
  ((nnnorm_on_K x) : ℝ) = norm_on_K x := rfl

@[ext]
lemma nnnorm_ext_norm {K : Type*} [field K] [mixed_char_local_field p K] (x y : K) : 
  (nnnorm_on_K x) = (nnnorm_on_K y) ↔ norm_on_K x = norm_on_K y := subtype.ext_iff


--`[FAE]` The following `instance` will probably be PR'd soon in greater generality for all
-- integrally closed domains: see 
-- [https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/.E2.9C.94.20gcd_monoid]
instance  : normalized_gcd_monoid ℤ_[p] :=
begin
  classical,  
  have norm_monoid_Zp := @unique_factorization_monoid.normalization_monoid ℤ_[p] _ _ _,
  exact @unique_factorization_monoid.to_normalized_gcd_monoid ℤ_[p] _ _ norm_monoid_Zp _ _,
end

lemma norm_on_K_one {K : Type*} [field K] [mixed_char_local_field p K] : norm_on_K (1 : K) = 1 := 
by rw [norm_on_K, spectral_norm_is_norm_one_class]

variables (K)
-- variables (p K)

lemma norm_of_int_le_one (x : 𝓞 p K) : norm_on_K (x : K) ≤ 1 :=
begin
  let min_Z := minpoly ℤ_[p] x,
  have h_Z_monic := minpoly.monic (is_integral_closure.is_integral ℤ_[p] K x),
  let min_Q : polynomial ℚ_[p] := polynomial.map padic_int.coe.ring_hom min_Z,
  have h_Q_monic : monic min_Q := polynomial.monic.map padic_int.coe.ring_hom h_Z_monic,
  have is_minpoly : min_Q = @minpoly ℚ_[p] K _ _ _ (x : K),
  exact (minpoly.is_integrally_closed_eq_field_fractions ℚ_[p] K (is_integral_closure.is_integral
    ℤ_[p] K x)).symm,
  have : norm_on_K (x : K) = spectral_value min_Q,
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

lemma norm_on_K_p_lt_one (K : Type*) [field K] [mixed_char_local_field p K] :
  norm_on_K (p : K) < 1 :=
begin
  have hp : (p : K) = algebra_map ℚ_[p] K (p : ℚ_[p]),
  { simp only [subring_class.coe_nat_cast, map_nat_cast] },
  rw [norm_on_K, hp, spectral_norm_extends (p : ℚ_[p])],
  exact padic_norm_e.norm_p_lt_one,
end

def open_unit_ball : height_one_spectrum (𝓞 p K) :=
{ as_ideal := 
  { carrier   := { x : 𝓞 p K | norm_on_K (x : K) < 1},
    add_mem'  := λ x y hx hy,
    begin
      rw [set.mem_set_of_eq, norm_on_K] at hx hy ⊢,
      refine lt_of_le_of_lt (spectral_norm_is_nonarchimedean 
        (algebra.is_algebraic_of_finite ℚ_[p] K) padic_norm_e.nonarchimedean (x : K)
        (y : K)) (max_lt_iff.mpr ⟨hx, hy⟩),
    end,  
    zero_mem' := 
    begin
      rw [set.mem_set_of_eq, zero_mem_class.coe_zero, norm_on_K, spectral_norm_zero],
      exact zero_lt_one,
    end,
    smul_mem' := λ k x hx,
    begin
      rw [norm_on_K, smul_eq_mul, set.mem_set_of_eq, mul_mem_class.coe_mul,
        ← spectral_alg_norm_def (algebra.is_algebraic_of_finite ℚ_[p] K)
          padic_norm_e.nonarchimedean,
        spectral_norm_is_mul (algebra.is_algebraic_of_finite ℚ_[p] K)
          padic_norm_e.nonarchimedean (k : K) (x : K)],
      exact mul_lt_one_of_nonneg_of_lt_one_right (norm_of_int_le_one K k)
        (spectral_norm_nonneg _) hx,
    end },
  is_prime := 
  begin
    rw ideal.is_prime_iff,
    split,
    { rw ideal.ne_top_iff_one,
      simp only [set.mem_set_of_eq, submodule.mem_mk, one_mem_class.coe_one, not_lt],
      exact le_of_eq (norm_on_K_one).symm, },
    { intros x y hxy,
      simp only [set.mem_set_of_eq, submodule.mem_mk, mul_mem_class.coe_mul] at hxy ⊢,
      rw [norm_on_K, ← spectral_alg_norm_def (algebra.is_algebraic_of_finite ℚ_[p] K) 
        padic_norm_e.nonarchimedean, spectral_norm_is_mul (algebra.is_algebraic_of_finite ℚ_[p] K) 
        padic_norm_e.nonarchimedean] at hxy, 
      contrapose! hxy,
      exact one_le_mul_of_one_le_of_one_le hxy.1 hxy.2,  }
  end,
  ne_bot   := --TODO: golf
  begin
    apply ne_of_gt,
    split,
    { simp only [submodule.bot_coe, submodule.coe_set_mk, set.singleton_subset_iff,
        set.mem_set_of_eq, zero_mem_class.coe_zero, norm_on_K, spectral_norm_zero],
      exact zero_lt_one, }, 
    { simp only [submodule.coe_set_mk, submodule.bot_coe, set.subset_singleton_iff,
        set.mem_set_of_eq, not_forall, exists_prop], 
      refine ⟨(p : 𝓞 p K), _, ne_zero.ne ↑p⟩,
      have : ((p : 𝓞 p K) : K) = algebra_map ℚ_[p] K (p : ℚ_[p]) :=
        by {simp only [subring_class.coe_nat_cast, map_nat_cast]},
      rw [norm_on_K, this, spectral_norm_extends (p : ℚ_[p])],
      exact padic_norm_e.norm_p_lt_one }
  end }

def normalized_valuation (K : Type*) [field K] [mixed_char_local_field p K] : valuation K ℤₘ₀ :=
(open_unit_ball K).valuation

@[priority 100]
instance (K : Type*) [field K] [mixed_char_local_field p K] : valued K ℤₘ₀ :=
valued.mk' (normalized_valuation K)

instance (K : Type*) [field K] [mixed_char_local_field p K] : 
  is_discrete (mixed_char_local_field.with_zero.valued K).v :=
sorry

lemma normalized_valuation_p_ne_zero : (normalized_valuation K) (p : K) ≠ 0 :=
by {simp only [ne.def, valuation.zero_iff, nat.cast_eq_zero], from nat.prime.ne_zero (fact.out _)}

--TODO: turn into lemma
open multiplicative is_dedekind_domain.height_one_spectrum
def ramification_index (K : Type*) [field K] [mixed_char_local_field p K] : ℤ := 
  -(with_zero.unzero (normalized_valuation_p_ne_zero K)).to_add

localized "notation (name := ramification_index)
  `e` := mixed_char_local_field.ramification_index" in mixed_char_local_field

variable (p)

lemma padic.mem_integers_iff (y : ℚ_[p]) : y ∈ 𝓞 p ℚ_[p] ↔ ‖ y ‖ ≤ 1 :=
begin
  rw [mem_ring_of_integers, is_integrally_closed.is_integral_iff],
  refine ⟨λ h, _, λ h, ⟨⟨y, h⟩, rfl⟩⟩,
  { obtain ⟨x, hx⟩ := h,
    rw [← hx],
    exact padic_int.norm_le_one _ }
end

lemma padic.norm_le_one_iff_val_le_one (y : ℚ_[p]) : ‖ y ‖ ≤ 1 ↔ valued.v y ≤ (1 : ℤₘ₀) :=
begin
  rw ← rank_one_valuation.norm_le_one_iff_val_le_one y,
  sorry
  
end

#exit

-- Even compiling the statement is slow...
noncomputable! lemma padic.open_unit_ball_def : 
  (open_unit_ball ℚ_[p]).as_ideal = ideal.span {(p : 𝓞 p ℚ_[p])} := 
begin
  have hiff : ∀ (y : ℚ_[p]), y ∈ 𝓞 p ℚ_[p] ↔ ‖ y ‖  ≤ 1 := padic.mem_integers_iff p,
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
    exact hcx },
end

variable {p}

--set_option profiler true
lemma is_unramified_ℚ_p : e ℚ_[p] = 1 :=
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
  rw [ramification_index, neg_eq_iff_eq_neg, ← to_add_of_add (-1 : ℤ)],
  apply congr_arg,
  rw [← with_zero.coe_inj, ← hp, with_zero.coe_unzero],
end

variable (p)
def padic_int.equiv_valuation_subring : 
  ℤ_[p] ≃+* ↥(mixed_char_local_field.with_zero.valued ℚ_[p]).v.valuation_subring := 
{ to_fun    := λ x,
  begin
    use x.1, rw mem_valuation_subring_iff,
    --exact (padic.mem_integers_iff _ _).mpr x.2,
    sorry,
  end,
  inv_fun   := sorry,
  left_inv  := sorry,
  right_inv := sorry,
  map_mul'  := sorry,
  map_add'  := sorry }

variable {p}

lemma padic_int.equiv_valuation_subring_comm :
  (algebra_map ↥(valued.v.valuation_subring) K).comp 
    (padic_int.equiv_valuation_subring p).to_ring_hom = algebra_map ℤ_[p] K :=
sorry

instance : discrete_valuation_ring (𝓞 p K) := 
begin
  letI : complete_space ℚ_[p] := sorry,
  letI : discrete_valuation_ring 
    (integral_closure (mixed_char_local_field.with_zero.valued ℚ_[p]).v.valuation_subring K) :=
  dvr_of_finite_extension ℚ_[p] K,
  have heq : (𝓞 p K).to_subring = (integral_closure 
    (mixed_char_local_field.with_zero.valued ℚ_[p]).v.valuation_subring K).to_subring,
  { ext x,
    simp only [subalgebra.mem_to_subring, mem_ring_of_integers, mem_integral_closure_iff],
    apply is_integral_iff_of_equiv (padic_int.equiv_valuation_subring p)
      (padic_int.equiv_valuation_subring_comm K), },
  set φ : (integral_closure 
    (mixed_char_local_field.with_zero.valued ℚ_[p]).v.valuation_subring K) ≃+* 𝓞 p K :=
  ring_equiv.subring_congr heq.symm,
  exact ring_equiv.discrete_valuation_ring φ,
end

-- TODO : ring of integers is local
noncomputable!  instance : local_ring (𝓞 p K) :=
infer_instance

end mixed_char_local_field
