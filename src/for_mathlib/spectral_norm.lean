import data.list.min_max
import analysis.special_functions.pow
import ring_theory.algebraic
import field_theory.minpoly

noncomputable theory

open polynomial

open_locale polynomial

variables {R : Type*} [normed_ring R]

def polynomial.coeffs (p : R[X])  : list R := list.map p.coeff (list.range p.nat_degree)

lemma list.le_max_of_exists_le {α : Type*} [linear_order α] {l : list α} {a x : α} (b : α)
  (hx : x ∈ l) (h : a ≤ x) : a ≤ l.foldr max b :=
begin
  induction l with y l IH,
  { exact absurd hx (list.not_mem_nil _), },
  { obtain rfl | hl := hx,
    simp only [list.foldr, list.foldr_cons],
    { exact le_max_of_le_left h, },
    { exact le_max_of_le_right (IH hl) }}
end

def spectral_value_terms {p : R[X]} (hp : p.monic) : ℕ → ℝ := 
λ (n : ℕ), if n < p.nat_degree then ∥ p.coeff n ∥^(1/(p.nat_degree - n : ℝ)) else 0

lemma spectral_value_terms_of_lt_nat_degree {p : R[X]} (hp : p.monic) {n : ℕ}
  (hn : n < p.nat_degree) : spectral_value_terms hp n = ∥ p.coeff n ∥^(1/(p.nat_degree - n : ℝ)) := 
by simp only [spectral_value_terms, if_pos hn]

lemma spectral_value_terms_of_nat_degree_le {p : R[X]} (hp : p.monic) {n : ℕ}
  (hn : p.nat_degree ≤ n) : spectral_value_terms hp n = 0 := 
by simp only [spectral_value_terms, if_neg (not_lt.mpr hn)]

def spectral_value {p : R[X]} (hp : p.monic) : ℝ := supr (spectral_value_terms hp)

lemma spectral_value_terms_bdd_above {p : R[X]} (hp : p.monic) :
  bdd_above (set.range (spectral_value_terms hp)) := 
begin
  use list.foldr max 0
  (list.map (λ n, ∥ p.coeff n ∥^(1/(p.nat_degree - n : ℝ))) (list.range p.nat_degree)),
  { rw mem_upper_bounds,
    intros r hr,
    obtain ⟨n, hn⟩ := set.mem_range.mpr hr,
    simp only [spectral_value_terms] at hn,

    split_ifs at hn with hd hd,
    { have h : ∥p.coeff n∥ ^ (1 / (p.nat_degree - n : ℝ)) ∈ list.map 
        (λ (n : ℕ), ∥p.coeff n∥ ^ (1 / (p.nat_degree - n : ℝ))) (list.range p.nat_degree),
      { simp only [list.mem_map, list.mem_range],
        exact ⟨n, hd, rfl⟩, },
    exact list.le_max_of_exists_le 0 h (ge_of_eq hn), },
    { rw ← hn,
      by_cases hd0 : p.nat_degree = 0,
      { rw [hd0, list.range_zero, list.map_nil, list.foldr_nil], },
      { have h : ∥p.coeff 0∥ ^ (1 / (p.nat_degree - 0 : ℝ)) ∈ list.map 
          (λ (n : ℕ), ∥p.coeff n∥ ^ (1 / (p.nat_degree - n : ℝ))) (list.range p.nat_degree),
        { simp only [list.mem_map, list.mem_range],
          exact ⟨0, nat.pos_of_ne_zero hd0, by rw nat.cast_zero⟩,},
      refine list.le_max_of_exists_le 0 h _,
      exact real.rpow_nonneg_of_nonneg (norm_nonneg _) _}}},
end

lemma spectral_value_terms_finite_range {p : R[X]} (hp : p.monic) :
  (set.range (spectral_value_terms hp)).finite :=
begin
  have h_ss : set.range (spectral_value_terms hp) ⊆ set.range (λ (n : fin p.nat_degree), 
    ∥ p.coeff n ∥^(1/(p.nat_degree - n : ℝ))) ∪ {(0 : ℝ)},
  { intros x hx,
    obtain ⟨m, hm⟩ := set.mem_range.mpr hx,
    by_cases hm_lt : m < p.nat_degree,
    { simp only [spectral_value_terms_of_lt_nat_degree hp hm_lt] at hm,
      rw ← hm,
      exact set.mem_union_left _ ⟨⟨m, hm_lt⟩, rfl⟩, },
    { simp only [spectral_value_terms_of_nat_degree_le hp (le_of_not_lt hm_lt)] at hm,
      rw hm,
      exact set.mem_union_right _ (set.mem_singleton _), }},
  exact set.finite.subset (set.finite.union (set.finite_range _) (set.finite_singleton _)) h_ss,
end

lemma spectral_value_terms_nonneg {p : R[X]} (hp : p.monic) (n : ℕ) :
  0 ≤ spectral_value_terms hp n :=
begin
  simp only [spectral_value_terms],
  split_ifs with h,
  { exact real.rpow_nonneg_of_nonneg (norm_nonneg _) _ },
  { exact le_refl _ },
end

variable [nontrivial R]

lemma list.max_repeat {α : Type*} {n : ℕ} (a : α) [linear_order α] :
  list.foldr max a (list.repeat a n) = a :=
begin
  induction n with n hn,
  { simp only [list.repeat, list.foldr_nil] },
  { simp only [list.foldr, list.repeat, list.repeat_succ, list.foldr_cons, max_eq_left_iff],
    exact le_of_eq hn, }
end

lemma spectral_value_X_pow (n : ℕ) :
  spectral_value (@polynomial.monic_X_pow R _ n) = 0 := 
begin
  rw spectral_value, rw spectral_value_terms,
  simp_rw [polynomial.coeff_X_pow n, polynomial.nat_degree_X_pow],
  convert csupr_const,
  ext m,
  by_cases hmn : m < n,
  { rw [if_pos hmn, real.rpow_eq_zero_iff_of_nonneg (norm_nonneg _), if_neg (ne_of_lt hmn),
      norm_zero, one_div, ne.def, inv_eq_zero, ← nat.cast_sub (le_of_lt hmn), nat.cast_eq_zero,
      nat.sub_eq_zero_iff_le],
    exact ⟨eq.refl _, not_le_of_lt hmn⟩ },
  { rw if_neg hmn },
  apply_instance,
end

lemma spectral_value_eq_zero_iff [nontrivial R] {p : R[X]} (hp : p.monic) :
  spectral_value hp = 0 ↔ p = polynomial.X^p.nat_degree := 
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rw spectral_value at h,
    ext,
    rw polynomial.coeff_X_pow,
    by_cases hn : n = p.nat_degree,
    { rw [if_pos hn, hn, polynomial.coeff_nat_degree], exact hp, },
    { rw if_neg hn,
      { by_cases hn' : n < p.nat_degree,
        { have h_le : supr (spectral_value_terms hp) ≤ 0 := le_of_eq h,
          have h_exp : 0 < 1 / ((p.nat_degree : ℝ) - n),
          { rw [one_div_pos, ← nat.cast_sub (le_of_lt hn'), nat.cast_pos],
            exact nat.sub_pos_of_lt hn', },
          have h0 : (0 : ℝ) = 0^(1 / ((p.nat_degree : ℝ) - n)),
          { rw real.zero_rpow (ne_of_gt h_exp), },
          rw [supr, cSup_le_iff (spectral_value_terms_bdd_above hp)
            (set.range_nonempty _)] at h_le,
          specialize h_le (spectral_value_terms hp n) ⟨n, rfl⟩,
          simp only [spectral_value_terms, if_pos hn'] at h_le,
          rw [h0, real.rpow_le_rpow_iff (norm_nonneg _) (le_refl _) h_exp] at h_le,
          exact norm_eq_zero.mp (le_antisymm h_le (norm_nonneg _)), },
        { exact polynomial.coeff_eq_zero_of_nat_degree_lt 
            (lt_of_le_of_ne (le_of_not_lt hn') (ne_comm.mpr hn)) }}}},
  { convert spectral_value_X_pow p.nat_degree,
    apply_instance }
end

lemma spectral_value_X_sub_C (r : R) :
  spectral_value (@polynomial.monic_X_sub_C _ _ r) = ∥r∥ := 
begin
  rw spectral_value, rw spectral_value_terms,
  simp only [polynomial.nat_degree_X_sub_C, nat.lt_one_iff, polynomial.coeff_sub,
    nat.cast_one, one_div],
  suffices : (⨆ (n : ℕ), ite (n = 0) ∥r∥ 0) = ∥r∥,
  { rw ← this,
    apply congr_arg,
    ext n,
    by_cases hn : n = 0,
    { rw [if_pos hn, if_pos hn, hn, nat.cast_zero, sub_zero, polynomial.coeff_X_zero,
        polynomial.coeff_C_zero, zero_sub, norm_neg, inv_one, real.rpow_one] },
    { rw [if_neg hn, if_neg hn], }},
  { apply csupr_eq_of_forall_le_of_forall_lt_exists_gt,
    { intro n,
      split_ifs,
      exact le_refl _, 
      exact norm_nonneg _ },
    { intros x hx, use 0,
      simp only [eq_self_iff_true, if_true, hx], }}
end

section spectral_norm

variables {K : Type*} [normed_field K] {L : Type*} [field L] [algebra K L]
(h_alg : algebra.is_algebraic K L)

-- The spectral norm |y|_sp is the spectral value of the minimal polynomial of y over K.
def spectral_norm (y : L) : ℝ :=
spectral_value (minpoly.monic (is_algebraic_iff_is_integral.mp (h_alg y)))

lemma spectral_norm_zero : spectral_norm h_alg (0 : L) = 0 := 
begin
  have h_lr: list.range 1 = [0] := rfl,
  rw [spectral_norm, spectral_value, spectral_value_terms, minpoly.zero, polynomial.nat_degree_X],
  convert csupr_const,
  ext m,
  by_cases hm : m < 1,
  { rw [if_pos hm, nat.lt_one_iff.mp hm, nat.cast_one, nat.cast_zero, sub_zero,
      div_one, real.rpow_one, polynomial.coeff_X_zero, norm_zero] },
  { rw if_neg hm },
  apply_instance,
end

lemma spectral_norm_nonneg (y : L) : 0 ≤  spectral_norm h_alg y := 
le_csupr_of_le (spectral_value_terms_bdd_above (minpoly.monic
  (is_algebraic_iff_is_integral.mp (h_alg y)))) 0 (spectral_value_terms_nonneg _ 0)

lemma spectral_norm.zero_lt {y : L} (hy : y ≠ 0) : 0 < spectral_norm h_alg y := 
begin
  rw lt_iff_le_and_ne,
  refine ⟨spectral_norm_nonneg _ _, _⟩,
  rw [spectral_norm, ne.def, eq_comm, spectral_value_eq_zero_iff],
  have h0 : polynomial.coeff (minpoly K y) 0 ≠ 0  :=
  minpoly.coeff_zero_ne_zero (is_algebraic_iff_is_integral.mp (h_alg y)) hy,
  intro h,
  have h0' : (minpoly K y).coeff 0 = 0,
  { rw [h, polynomial.coeff_X_pow,
      if_neg (ne_of_lt ( minpoly.nat_degree_pos (is_algebraic_iff_is_integral.mp (h_alg y))))] },
  exact h0 h0', 
end

lemma spectral_norm.smul (k : K) (y : L) (hna : ∀ (r s : K), ∥r + s∥ ≤ (max ∥r∥ ∥s∥)) :
  spectral_norm h_alg (k • y) = ∥ k ∥ * spectral_norm h_alg y :=
sorry

lemma spectral_norm.is_nonarchimedean (hna : ∀ (r s : K), ∥r + s∥ ≤ (max ∥r∥ ∥s∥)) (x y : L) :
  spectral_norm h_alg (x + y) ≤ max (spectral_norm h_alg x) (spectral_norm h_alg y)  :=
sorry

lemma spectral_norm.mul (x y : L) (hna : ∀ (r s : K), ∥r + s∥ ≤ (max ∥r∥ ∥s∥)) :
  spectral_norm h_alg (x * y) = spectral_norm h_alg x * spectral_norm h_alg y :=
sorry

lemma spectral_norm.extends (k : K) : spectral_norm h_alg (algebra_map K L k) = ∥ k ∥ :=
begin
  simp_rw [spectral_norm, minpoly.eq_X_sub_C_of_algebra_map_inj _ (algebra_map K L).injective],
  exact spectral_value_X_sub_C k,
end

lemma spectral_norm.aut_isom (σ : L ≃ₐ[K] L) (x : L) : 
  spectral_norm h_alg x = spectral_norm h_alg (σ x) :=
sorry

end spectral_norm
