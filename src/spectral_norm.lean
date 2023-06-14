--import analysis.special_functions.pow.nnreal
import from_mathlib.spectral_norm_unique

open_locale nnreal polynomial

open polynomial

section spectral_value

variables {S : Type*} [normed_division_ring S]

lemma spectral_value_le_one_iff {P : S[X]} (hP : monic P) : 
  spectral_value P ≤ 1 ↔ ∀ n : ℕ , ‖P.coeff n‖ ≤ 1 :=
begin
  rw spectral_value,
  split; intro h,
  { intros n,
    by_contradiction hn,
    rw not_le at hn,
    have hsupr : 1 < supr (spectral_value_terms P),
    { have hn' : 1 < spectral_value_terms P n,
      { simp only [spectral_value_terms],
        split_ifs with hPn,
        { apply real.one_lt_rpow hn,
          simp only [one_div, inv_pos, sub_pos, nat.cast_lt],
          exact hPn },
        { rw [not_lt, le_iff_lt_or_eq] at hPn,
          cases hPn with hlt heq,
          { rw [coeff_eq_zero_of_nat_degree_lt hlt, norm_zero] at hn,
            exfalso, linarith, },
          { rw [monic, leading_coeff, heq] at hP,
            rw [hP, norm_one] at hn,
            linarith, }}},
      exact lt_csupr_of_lt (spectral_value_terms_bdd_above P) n hn', },
    linarith, },
  { simp only [spectral_value_terms],
    apply csupr_le,
    intros n,
    split_ifs with hn,
    { apply real.rpow_le_one (norm_nonneg _) (h n),
      rw [one_div_nonneg,sub_nonneg, nat.cast_le],
      exact le_of_lt hn, },
    { exact zero_le_one }},
end

end spectral_value

open finite_dimensional

variables {K : Type*} [nontrivially_normed_field K] [complete_space K] 
  (hna : is_nonarchimedean (norm : K → ℝ)) {L : Type*} [field L] [algebra K L]
   --[finite_dimensional K L]

/- lemma spectral_value_term_le (x : L) {n : ℕ} (hn : n < (minpoly K x).nat_degree)  :
  ‖(minpoly K x).coeff n‖ ^ (1 / (((minpoly K x).nat_degree : ℝ) - n)) ≤ 
  ‖(minpoly K x).coeff 0‖ ^ (1 / ((minpoly K x).nat_degree : ℝ)) :=
sorry

lemma spectral_norm_eq_root_zero_coeff (h_alg : algebra.is_algebraic K L) (x : L) :
  spectral_norm K L x = ‖ (minpoly K x).coeff 0‖^(1/(minpoly K x).nat_degree : ℝ) :=
begin
  simp only [spectral_norm, spectral_value, spectral_value_terms],
  apply le_antisymm,
  { apply csupr_le,
    intros n,
    split_ifs with hn,
    { exact spectral_value_term_le x hn, },
    { exact real.rpow_nonneg_of_nonneg (norm_nonneg _ ) _ }},
  { apply le_csupr_of_le (spectral_value_terms_bdd_above (minpoly K x)) 0,
    simp only [spectral_value_terms],
    rw [if_pos (minpoly.nat_degree_pos (is_algebraic_iff_is_integral.mp (h_alg x))),
      nat.cast_zero,  tsub_zero] }
end -/

lemma real.eq_rpow_one_div_iff {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) {z : ℝ} (hz : z ≠ 0) :
  x = y ^ (1 / z) ↔ x ^ z = y :=
begin
  have hx' : x = (⟨x, hx⟩ : ℝ≥0) := rfl,
  have hy' : y = (⟨y, hy⟩ : ℝ≥0) := rfl,
  rw [hx', hy', ← nnreal.coe_rpow, ← nnreal.coe_rpow, nnreal.coe_eq, nnreal.coe_eq,
    nnreal.eq_rpow_one_div_iff hz],
end

open polynomial 
lemma spectral_norm_eq_root_zero_coeff (h_alg : algebra.is_algebraic K L) 
 (hna : is_nonarchimedean (norm : K → ℝ)) (x : L) :
  spectral_norm K L x = ‖ (minpoly K x).coeff 0 ‖^(1/(minpoly K x).nat_degree : ℝ) :=
begin
  have hspl : splits  (ring_hom.id L) (map_alg K L (minpoly K x)),
  { sorry },
  have h0 : (algebra_map K L ((minpoly K x).coeff 0)) = (map_alg K L (minpoly K x)).coeff 0,
  { rw [map_alg_eq_map, coeff_map] },
  rw real.eq_rpow_one_div_iff (spectral_norm_nonneg x)
    (norm_nonneg ((minpoly K x).coeff 0)),
  rw [real.rpow_nat_cast],  
  rw ← @spectral_norm_extends K _ L _ _ ((minpoly K x).coeff 0),
  rw ← spectral_mul_ring_norm_def h_alg hna,
  rw ← spectral_mul_ring_norm_def h_alg hna,
  rw h0,
  rw polynomial.prod_roots_eq_coeff_zero_of_monic_of_split _ hspl,
  rw [map_mul, map_pow, map_neg_eq_map, map_one, one_pow, one_mul],
  simp only [polynomial.roots],
  simp only [multiset.empty_eq_zero],
  rw dif_neg,
  -- polynomial.degree_eq_card_roots
  sorry,
  { sorry },
  { have h_monic: (minpoly K x).leading_coeff = 1,
    { exact minpoly.monic (is_algebraic_iff_is_integral.mp (h_alg x)),},
    rw [map_alg_eq_map, monic, leading_coeff, coeff_map, nat_degree_map, 
      coeff_nat_degree, h_monic, map_one] },
  { rw [ne.def, nat.cast_eq_zero],
    exact ne_of_gt 
      (minpoly.nat_degree_pos (is_algebraic_iff_is_integral.mp (h_alg x))) },
end

lemma spectral_value_term_le (h_alg : algebra.is_algebraic K L) 
  (hna : is_nonarchimedean (norm : K → ℝ)) (x : L) {n : ℕ} (hn : n < (minpoly K x).nat_degree) :
  ‖(minpoly K x).coeff n‖ ^ (1 / (((minpoly K x).nat_degree : ℝ) - n)) ≤ 
  ‖(minpoly K x).coeff 0‖ ^ (1 / ((minpoly K x).nat_degree : ℝ)) :=
begin
  rw ← spectral_norm_eq_root_zero_coeff h_alg hna,
  simp only [spectral_norm, spectral_value, spectral_value_terms], 
  apply le_csupr_of_le (spectral_value_terms_bdd_above (minpoly K x)) n,
  simp only [spectral_value_terms, if_pos hn]
end