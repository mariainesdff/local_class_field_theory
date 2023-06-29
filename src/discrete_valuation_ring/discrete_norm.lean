/-
Copyright (c) 2023 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import discrete_valuation_ring.basic
import for_mathlib.field_theory.minpoly.normal
--import for_mathlib.ring_theory.valuation.int_polynomial
--import for_mathlib.ring_theory.valuation.minpoly
import spectral_norm

noncomputable theory

open discrete_valuation multiplicative finite_dimensional minpoly polynomial valuation with_zero

open_locale discrete_valuation nnreal

section aux_lemma

variables {K : Type*} [field K] {v : valuation K ℤₘ₀} {L : Type*} [field L] [algebra K L] 

lemma map_pow_div [finite_dimensional K L] (x : Lˣ) : 
  (with_zero_mult_int_to_nnreal (base_ne_zero K v)) 
    (v ((minpoly K (x : L)).coeff 0) ^ (finrank K L / (minpoly K (x : L)).nat_degree)) =
  ((with_zero_mult_int_to_nnreal (base_ne_zero K v)) 
    (v ((minpoly K (x : L)).coeff 0)) ^ 
    (1 / ((minpoly K (x : L)).nat_degree : ℝ))) ^ (finrank K L : ℝ) :=
begin
  have h_alg : algebra.is_algebraic K L := algebra.is_algebraic_of_finite K L,
  rw [_root_.map_pow, ← nnreal.rpow_nat_cast,
   nat.cast_div (minpoly.degree_dvd (is_algebraic_iff_is_integral.mp (h_alg ↑x)))
    (nat.cast_ne_zero.mpr (ne_of_gt (minpoly.nat_degree_pos 
    (is_algebraic_iff_is_integral.mp (h_alg ↑x))))), div_eq_mul_inv, mul_comm (finrank K L : ℝ),
    nnreal.rpow_mul, ← one_div],
  apply_instance,
end

end aux_lemma

namespace discrete_valuation

variables (K : Type*) [field K] [hv : valued K ℤₘ₀] [is_discrete hv.v]

include hv

section discrete_norm

definition discretely_normed_field : normed_field K :=
rank_one_valuation.valued_field.to_normed_field K ℤₘ₀

def nontrivially_discretely_normed_field : nontrivially_normed_field K :=
{ non_trivial := 
  begin
    obtain ⟨x, hx⟩ := exists_uniformizer hv.v,
    use x.1⁻¹,
    erw [@norm_inv K (@normed_field.to_normed_division_ring K (discretely_normed_field K)),
      one_lt_inv_iff, rank_one_valuation.norm_lt_one_iff_val_lt_one,
      rank_one_valuation.norm_pos_iff_val_pos],
    exact ⟨uniformizer_valuation_pos hv.v hx, uniformizer_valuation_lt_one hv.v hx⟩,
  end,
  ..(@rank_one_valuation.valued_field.to_normed_field K _ ℤₘ₀ _ _
      (discrete_valuation.is_rank_one _)) } 

def has_discrete_norm : has_norm K :=begin
  letI : nontrivially_normed_field K := nontrivially_discretely_normed_field K,
  apply_instance,
end

def discretely_semi_normed_comm_ring : semi_normed_comm_ring K :=
begin
  letI : nontrivially_normed_field K := nontrivially_discretely_normed_field K,
  apply_instance,
end

def discretely_semi_normed_ring : semi_normed_ring K :=
begin
  letI : nontrivially_normed_field K := nontrivially_discretely_normed_field K,
  apply_instance,
end

lemma norm_is_nonarchimedean : is_nonarchimedean (@norm K (has_discrete_norm K)) := 
λ x y, rank_one_valuation.norm_def_add_le x y

lemma norm_le_one_iff_val_le_one (x : K) : 
  (@norm K (has_discrete_norm K)) x ≤ 1 ↔ valued.v x ≤ (1 : ℤₘ₀) :=
rank_one_valuation.norm_le_one_iff_val_le_one x

variables {K} [complete_space K] {L : Type*} [field L] [algebra K L] 

def discrete_norm_extension (h_alg : algebra.is_algebraic K L) : 
  @mul_algebra_norm K (discretely_semi_normed_comm_ring K) L _ _ :=
@spectral_mul_alg_norm K (nontrivially_discretely_normed_field K) L _ _ h_alg _ 
  (norm_is_nonarchimedean K)

def discretely_normed_field_extension (h_alg : algebra.is_algebraic K L) : normed_field L :=
@spectral_norm_to_normed_field K (nontrivially_discretely_normed_field K) L _ _ _ h_alg 
  (norm_is_nonarchimedean K)

def discretely_normed_field_extension_uniform_space (h_alg : algebra.is_algebraic K L) : 
  uniform_space L :=
by haveI := discretely_normed_field_extension h_alg; apply_instance


namespace discrete_norm_extension

lemma zero (h_alg : algebra.is_algebraic K L) : discrete_norm_extension h_alg 0 = 0 :=
@spectral_norm_zero K (discretely_normed_field K) L _ _

lemma eq_root_zero_coeff (h_alg : algebra.is_algebraic K L) (x : L) :
  discrete_norm_extension h_alg x = (with_zero_mult_int_to_nnreal (base_ne_zero K hv.v)
    (valued.v ((minpoly K x).coeff 0)))^(1/(minpoly K x).nat_degree : ℝ) :=
@spectral_norm_eq_root_zero_coeff K (nontrivially_discretely_normed_field K) _ L _ _ h_alg
  (norm_is_nonarchimedean K) x

lemma pow_eq_pow_root_zero_coeff' (h_alg : algebra.is_algebraic K L) (x : L) (n : ℕ) : 
  (discrete_norm_extension h_alg x)^n = (with_zero_mult_int_to_nnreal (base_ne_zero K hv.v) 
    (valued.v ((minpoly K x).coeff 0)) ^ (n/(minpoly K x).nat_degree : ℝ)) :=
by rw [div_eq_inv_mul, real.rpow_mul nnreal.zero_le_coe, eq_root_zero_coeff,
    inv_eq_one_div, real.rpow_nat_cast]

lemma pow_eq_pow_root_zero_coeff (h_alg : algebra.is_algebraic K L) (x : L) {n : ℕ} 
  (hn : (minpoly K x).nat_degree ∣ n) : 
  (discrete_norm_extension h_alg x)^n = (with_zero_mult_int_to_nnreal (base_ne_zero K hv.v) 
    (valued.v ((minpoly K x).coeff 0)) ^ (n/(minpoly K x).nat_degree)) :=
begin
  nth_rewrite 1 [← real.rpow_nat_cast],
  rw [nat.cast_div hn (nat.cast_ne_zero.mpr
    (ne_of_gt (minpoly.nat_degree_pos (is_algebraic_iff_is_integral.mp (h_alg x)))))],
  exact pow_eq_pow_root_zero_coeff' h_alg x n,
  { apply_instance }
end

lemma nonneg (h_alg : algebra.is_algebraic K L) (x : L) : 0 ≤ discrete_norm_extension h_alg x :=
@spectral_norm_nonneg K (discretely_normed_field K) L _ _ _

lemma is_nonarchimedean (h_alg : algebra.is_algebraic K L) :
  is_nonarchimedean (discrete_norm_extension h_alg) :=
@spectral_norm_is_nonarchimedean K (discretely_normed_field K) L _ _ h_alg 
  (norm_is_nonarchimedean K)

lemma mul (h_alg : algebra.is_algebraic K L) (x y : L) : (discrete_norm_extension h_alg (x * y)) = 
  (discrete_norm_extension h_alg x) * (discrete_norm_extension h_alg y) :=
@spectral_norm_is_mul K (nontrivially_discretely_normed_field K) L _ _ h_alg _ 
  (norm_is_nonarchimedean K) x y

lemma le_one_iff_integral_minpoly (h_alg : algebra.is_algebraic K L) (x : L) : 
  discrete_norm_extension h_alg x ≤ 1 ↔ (∀ n : ℕ , hv.v ((minpoly K x).coeff n) ≤ 1) :=
begin
  letI := nontrivially_discretely_normed_field K,
  have h : spectral_mul_alg_norm h_alg _ x = spectral_norm K L x, refl,
  rw [discrete_norm_extension, h, spectral_norm,
    spectral_value_le_one_iff (minpoly.monic (is_algebraic_iff_is_integral.mp (h_alg x)))],
  simp_rw norm_le_one_iff_val_le_one,
end

-- TODO : Type class inference doesn't work well on this section (explain in paper).
lemma of_integer [fr : is_fraction_ring hv.v.valuation_subring.to_subring K] 
  (h_alg : algebra.is_algebraic K L) (x : (integral_closure hv.v.valuation_subring.to_subring L)) : 
  discrete_norm_extension h_alg x =  @spectral_value K (discretely_semi_normed_ring K) 
    (polynomial.map (algebra_map hv.v.valuation_subring.to_subring K) 
      (minpoly hv.v.valuation_subring.to_subring x)) :=
begin
  letI := nontrivially_discretely_normed_field K,
  letI : valuation_ring hv.v.valuation_subring.to_subring := 
  hv.v.valuation_subring.valuation_ring,
  have is_minpoly :  minpoly K (x : L) =
    polynomial.map (algebra_map hv.v.valuation_subring.to_subring K) 
      (minpoly hv.v.valuation_subring.to_subring x),
  { rw eq_comm,
    exact minpoly_of_subring K L hv.v.valuation_subring.to_subring x, },
  have h_app : (spectral_mul_alg_norm h_alg _) ↑x = spectral_norm K L (x : L) := rfl,
  rw [discrete_norm_extension, h_app, spectral_norm, ← is_minpoly],
  all_goals { exact norm_is_nonarchimedean K},
end

lemma le_one_of_integer [fr : is_fraction_ring hv.v.valuation_subring.to_subring K] 
  (h_alg : algebra.is_algebraic K L) (x : (integral_closure hv.v.valuation_subring.to_subring L)) : 
  discrete_norm_extension h_alg x ≤ 1 :=
begin
  letI := nontrivially_discretely_normed_field K,
  letI : valuation_ring hv.v.valuation_subring.to_subring := 
  hv.v.valuation_subring.valuation_ring,
  let min_int := minpoly hv.v.valuation_subring.to_subring x,
  let min_x : polynomial K := polynomial.map (algebra_map _ _) min_int,
  rw of_integer,
  refine csupr_le _,
  intro n,
  simp only [spectral_value_terms],
  split_ifs with hn,
  { have coeff_coe : ∀ n : ℕ, min_x.coeff n = (min_int.coeff n) :=
    λ n, by { rw [polynomial.coeff_map], refl, },
    rw [coeff_coe n],
    apply real.rpow_le_one (norm_nonneg _),
    rw norm_le_one_iff_val_le_one K,
    exact (min_int.coeff n).property,
    { simp only [one_div, inv_nonneg, sub_nonneg, nat.cast_le],
      exact (le_of_lt hn) }},
  { exact zero_le_one },
end

end discrete_norm_extension

end discrete_norm

end discrete_valuation