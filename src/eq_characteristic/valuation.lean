/-
Copyright (c) 2022 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import eq_characteristic.basic
import from_mathlib.normed_valued
import from_mathlib.spectral_norm_unique
import normalized_valuation
import for_mathlib.rank_one_valuation
import discrete_valuation_ring.global_to_local

--import algebra.group.type_tags

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

section is_dedekind_domain

open_locale polynomial

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

variables {R : Type*} [comm_ring R] [is_domain R] [is_dedekind_domain R] (L : Type*) [field L]
  [algebra R L] [is_fraction_ring R L] (v : height_one_spectrum R)

open_locale classical

namespace is_dedekind_domain.height_one_spectrum

def valuation_base (R : Type*) [comm_ring R] [is_domain R] [is_dedekind_domain R] (L : Type*)
  [field L] [algebra R L] [is_fraction_ring R L] (v : height_one_spectrum R) : ℝ≥0 :=
@discrete_valuation.valuation_base (adic_completion L v) _ 
  (v.valued_adic_completion L) _

lemma valuation_base_def {R : Type*} [comm_ring R] [is_domain R] [is_dedekind_domain R] (L : Type*)
  [field L] [algebra R L] [is_fraction_ring R L] (v : height_one_spectrum R) :
  valuation_base R L v = (if 1 < nat.card
    (local_ring.residue_field (adic_completion_integers L v))
  then nat.card
    (local_ring.residue_field (adic_completion_integers L v))
  else 2) :=
rfl

lemma one_lt_valuation_base {R : Type*} [comm_ring R] [is_domain R] [is_dedekind_domain R]
  (L : Type*) [field L] [algebra R L] [is_fraction_ring R L] (v : height_one_spectrum R) : 
  1 < valuation_base R L v :=
@discrete_valuation.one_lt_valuation_base (adic_completion L v) _ (v.valued_adic_completion L) _

lemma valuation_base_ne_zero {R : Type*} [comm_ring R] [is_domain R] [is_dedekind_domain R]
  (L : Type*) [field L] [algebra R L] [is_fraction_ring R L] (v : height_one_spectrum R) : 
  valuation_base R L v ≠ 0:=
@discrete_valuation.valuation_base_ne_zero (adic_completion L v) _ (v.valued_adic_completion L) _

end is_dedekind_domain.height_one_spectrum

open is_dedekind_domain is_dedekind_domain.height_one_spectrum

def is_dedekind_domain.height_one_spectrum.valuation_is_rank_one :
  is_rank_one  (@valued.v L _ ℤₘ₀ _ v.adic_valued) := 
{ hom         := with_zero_mult_int_to_nnreal (valuation_base_ne_zero L v),
  strict_mono := with_zero_mult_int_to_nnreal_strict_mono (one_lt_valuation_base L v),
  nontrivial  := begin
    obtain ⟨x, hxv, hx0⟩ := submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot,
    use algebra_map L _ (algebra_map R L x),
    split,
    { rw [ne.def, valuation.zero_iff, _root_.map_eq_zero, ← map_zero (algebra_map R L), ←ne.def, 
        function.injective.ne_iff (no_zero_smul_divisors.algebra_map_injective R L)],
      exact hx0 },
    { apply ne_of_lt,
      erw is_dedekind_domain.height_one_spectrum.valuation_lt_one_iff_dvd,
      rw [ideal.dvd_span_singleton],
      exact hxv }
  end }

lemma is_dedekind_domain.height_one_spectrum.valuation_is_rank_one_hom_def :
  (@is_rank_one.hom L _ ℤₘ₀ _ (@valued.v L _ ℤₘ₀ _ v.adic_valued) 
    (is_dedekind_domain.height_one_spectrum.valuation_is_rank_one L v)) =
  with_zero_mult_int_to_nnreal (valuation_base_ne_zero L v) :=
rfl

def is_dedekind_domain.height_one_spectrum.valuation_completion_is_rank_one
  (hL : is_rank_one  (@valued.v L _ ℤₘ₀ _ v.adic_valued)) :
  is_rank_one  (@valued.v (is_dedekind_domain.height_one_spectrum.adic_completion L v) _ ℤₘ₀ _ _) := 
{ hom         := with_zero_mult_int_to_nnreal (valuation_base_ne_zero L v),
  strict_mono := with_zero_mult_int_to_nnreal_strict_mono (one_lt_valuation_base L v),
  nontrivial  := begin
    obtain ⟨x, hx0, hx1⟩ := hL.nontrivial,
    use algebra_map L _ x,
    split;
    rw [height_one_spectrum.valued_adic_completion_def,
        is_dedekind_domain.height_one_spectrum.algebra_map_adic_completion,
        valued.extension_extends],
    exacts [hx0, hx1],
  end }

lemma is_dedekind_domain.height_one_spectrum.valuation_completion_is_rank_one_hom_def :
  (@is_rank_one.hom (is_dedekind_domain.height_one_spectrum.adic_completion L v) _ ℤₘ₀ _ 
  (@valued.v (is_dedekind_domain.height_one_spectrum.adic_completion L v) _ ℤₘ₀ _ _)
    (is_dedekind_domain.height_one_spectrum.valuation_completion_is_rank_one L v
      (is_dedekind_domain.height_one_spectrum.valuation_is_rank_one L v))) =
  with_zero_mult_int_to_nnreal (valuation_base_ne_zero L v) :=
rfl

variables [hv : is_rank_one 
  (@valued.v (is_dedekind_domain.height_one_spectrum.adic_completion L v) _ ℤₘ₀ _ _)]

include hv 

instance : 
  normed_field (is_dedekind_domain.height_one_spectrum.adic_completion L v) :=
by apply rank_one_valuation.valued_field.to_normed_field
  (is_dedekind_domain.height_one_spectrum.adic_completion L v) ℤₘ₀ 

lemma norm_le_one_iff_val_le_one (x : is_dedekind_domain.height_one_spectrum.adic_completion L v) :
  ‖x‖ ≤ 1 ↔ valued.v x ≤ (1 : ℤₘ₀) :=
rank_one_valuation.norm_le_one_iff_val_le_one x

variables (R)

def int_polynomial {P : (is_dedekind_domain.height_one_spectrum.adic_completion L v)[X]}
  (hP : ∀ n : ℕ , ‖P.coeff n‖ ≤ 1) :
  (is_dedekind_domain.height_one_spectrum.adic_completion_integers L v)[X] := 
{ to_finsupp := 
  { support := P.support,
    to_fun := λ n, ⟨P.coeff n, (height_one_spectrum.mem_adic_completion_integers R L v).mp
       ((norm_le_one_iff_val_le_one L v _).mp (hP n))⟩,
    mem_support_to_fun := λ n, by rw [mem_support_iff, ne.def, not_iff_not, subtype.ext_iff,
      subring.coe_zero, subtype.coe_mk] }}

variables {R}

lemma int_polynomial_coeff_eq 
  {P : (is_dedekind_domain.height_one_spectrum.adic_completion L v)[X]}
  (hP : ∀ n : ℕ , ‖P.coeff n‖ ≤ 1) (n : ℕ) :
  ↑((int_polynomial R L v hP).coeff n) = P.coeff n :=
rfl

lemma int_polynomial_leading_coeff_eq 
  {P : (is_dedekind_domain.height_one_spectrum.adic_completion L v)[X]}
  (hP : ∀ n : ℕ , ‖P.coeff n‖ ≤ 1) :
  ↑((int_polynomial R L v hP).leading_coeff) = P.leading_coeff :=
rfl

lemma int_polynomial_nat_degree 
  {P : (is_dedekind_domain.height_one_spectrum.adic_completion L v)[X]}
  (hP : ∀ n : ℕ , ‖P.coeff n‖ ≤ 1) : (int_polynomial R L v hP).nat_degree = P.nat_degree :=
rfl

end is_dedekind_domain

variables {p : ℕ} [fact (p.prime)] 

namespace FpX_field_completion

instance : is_rank_one (@FpX_field_completion.with_zero.valued p _).v :=
is_dedekind_domain.height_one_spectrum.valuation_completion_is_rank_one _ _
  (is_dedekind_domain.height_one_spectrum.valuation_is_rank_one _ _)

instance : normed_field 𝔽_[p]⟮⟮X⟯⟯ := rank_one_valuation.valued_field.to_normed_field _ _

noncomputable! lemma residue_field_card_eq_char :
  nat.card (local_ring.residue_field 𝔽_[p]⟦X⟧) = p :=
begin
  rw FpX_int_completion,
  sorry
end

.

open is_dedekind_domain is_dedekind_domain.height_one_spectrum

lemma valuation_base_eq_char : 
  @valuation_base (polynomial 𝔽_[p]) _ _ _ (ratfunc 𝔽_[p]) _ _ _ (ideal_X 𝔽_[p]) = p :=
begin
  rw [valuation_base, discrete_valuation.valuation_base, if_pos],
  { sorry /- exact nat.cast_inj.mpr residue_field_card_eq_char,  -/},
  { sorry/-  erw residue_field_card_eq_char, 
    exact (fact.out (nat.prime p)).one_lt  -/},
end

variable (p)
def X := algebra_map 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯ (FpX_int_completion.X p)

lemma X_eq_coe : X p = ↑(@ratfunc.X 𝔽_[p] _ _) := rfl

variable {p}

lemma norm_X : ‖ X p ‖ = 1/(p : ℝ) :=
begin
  have hv : valued.v (X p) = multiplicative.of_add (-1 : ℤ),
  { rw [← val_X_eq_one 𝔽_[p], height_one_spectrum.valued_adic_completion_def,
      FpX_field_completion.X_eq_coe, valued.extension_extends], refl, },
  have hX : ‖X p‖ = is_rank_one.hom  _ (valued.v (X p)) := rfl,
  rw [hX, is_dedekind_domain.height_one_spectrum.valuation_completion_is_rank_one_hom_def, hv],
  simp only [of_add_neg, with_zero.coe_inv, map_inv₀, nonneg.coe_inv, one_div, inv_inj],
  simp only [ with_zero_mult_int_to_nnreal, with_zero_mult_int_to_nnreal_def, 
    monoid_with_zero_hom.coe_mk], 
  rw dif_neg,
  { simp only [with_zero.unzero_coe, to_add_of_add, zpow_one],
    rw valuation_base_eq_char, simp only [nnreal.coe_nat_cast], },
  { simp only [with_zero.coe_ne_zero, with_zero_mult_int_to_nnreal_strict_mono, not_false_iff] }
end

lemma norm_X_pos : 0 < ‖ X p ‖ :=
by rw [norm_X, one_div, inv_pos, nat.cast_pos]; exact (_inst_1.out).pos

lemma norm_X_lt_one : ‖ X p ‖ < 1 :=
by rw [norm_X, one_div]; exact inv_lt_one (nat.one_lt_cast.mpr (_inst_1.out).one_lt)

lemma X_mem_int_completion : X p ∈ FpX_int_completion p :=
begin
  rw [mem_FpX_int_completion, ← norm_le_one_iff_val_le_one],
  exact le_of_lt norm_X_lt_one, 
end

instance : nontrivially_normed_field 𝔽_[p]⟮⟮X⟯⟯ :=
{ non_trivial := begin
    use (X p)⁻¹,
    rw [norm_inv],
    exact one_lt_inv norm_X_pos norm_X_lt_one,
  end,
  ..(by apply_instance: normed_field 𝔽_[p]⟮⟮X⟯⟯) }

lemma norm_is_nonarchimedean : is_nonarchimedean (norm : 𝔽_[p]⟮⟮X⟯⟯ → ℝ) := 
rank_one_valuation.norm_def_is_nonarchimedean _ _

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

lemma norm_on_FpX_field_completion :
  ((norm_on_K ) : 𝔽_[p]⟮⟮X⟯⟯ → ℝ) = (norm : 𝔽_[p]⟮⟮X⟯⟯ → ℝ) := 
by { ext x, exact spectral_norm_extends _ }

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


lemma mem_FpX_int_completion' {x : FpX_field_completion p} :
  x ∈ FpX_int_completion p ↔ ‖ x ‖  ≤ 1 :=
by rw [FpX_field_completion.mem_FpX_int_completion, norm_le_one_iff_val_le_one]


lemma norm_on_K_of_int (x : 𝓞 p K) : norm_on_K (x : K) =
  spectral_value (polynomial.map (algebra_map 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯) (minpoly 𝔽_[p]⟦X⟧ x)) :=
begin
  have is_minpoly :  @minpoly 𝔽_[p]⟮⟮X⟯⟯ K _ _ _ (x : K) =
    polynomial.map (algebra_map _ _) (minpoly 𝔽_[p]⟦X⟧ x),
  { apply (minpoly.is_integrally_closed_eq_field_fractions 𝔽_[p]⟮⟮X⟯⟯ K
      (is_integral_closure.is_integral 𝔽_[p]⟦X⟧ K x)) },
  simp only [norm_on_K, spectral_norm, ← is_minpoly],
end

.

-- Really slow, I had to create the previous lemma to avoid a timeout.
lemma norm_of_int_le_one (x : 𝓞 p K) : norm_on_K (x : K) ≤ 1 :=
begin
  let min_int := minpoly 𝔽_[p]⟦X⟧ x,
  let min_x : polynomial 𝔽_[p]⟮⟮X⟯⟯ := polynomial.map (algebra_map _ _) min_int,
  rw norm_on_K_of_int x,
  refine csupr_le _,
  intro n,
  simp only [spectral_value_terms],
  split_ifs with hn,
  { have coeff_coe : ∀ n : ℕ, min_x.coeff n = (min_int.coeff n) :=
    λ n, by { simp only [polynomial.coeff_map, FpX_int_completion.algebra_map_eq_coe] },
    rw [coeff_coe n],
    apply real.rpow_le_one (norm_nonneg _),
    apply mem_FpX_int_completion'.mp (min_int.coeff n).property,
    simp only [one_div, inv_nonneg, sub_nonneg, nat.cast_le],
    exact (le_of_lt hn) },
  { exact zero_le_one }, 
end


lemma mem_ring_of_integers_iff_norm_le_one (x : K) : x ∈ 𝓞 p K ↔ norm_on_K (x : K) ≤ 1 :=
begin
  refine ⟨λ hx, by apply norm_of_int_le_one ⟨x, hx⟩, _⟩,
  { intro hx,
    have hmonic := minpoly.monic (is_algebraic_iff_is_integral.mp 
        (algebra.is_algebraic_of_finite 𝔽_[p]⟮⟮X⟯⟯ K x)),
    rw [norm_on_K, spectral_norm, spectral_value_le_one_iff hmonic] at hx,
    set P : polynomial ((FpX_int_completion p)) := 
    int_polynomial (polynomial 𝔽_[p]) (ratfunc 𝔽_[p]) (ideal_X 𝔽_[p]) hx with hP,
    rw [mem_ring_of_integers, is_integral, adic_algebra.int_algebra_map_def,
      ring_hom.is_integral_elem],
    use P,
    split,
    --TODO: extract general lemmas for int_polynomial
    { rw [monic, subtype.ext_iff, subring.coe_one, int_polynomial_leading_coeff_eq],
      apply hmonic },
    { have h : (eval₂ algebra.to_ring_hom x P) = aeval x (minpoly (FpX_field_completion p) x),
      { rw [aeval_eq_sum_range, eval₂_eq_sum_range],
        apply finset.sum_congr rfl,
        intros n hn,
        rw algebra.smul_def,
        refl, },
      rw [h, minpoly.aeval] }},
end


variables (K)

instance : complete_space 𝔽_[p]⟮⟮X⟯⟯ := uniform_space.completion.complete_space _


.

--TODO: move to basic file
lemma FpX_int_completion.X_ne_zero : FpX_int_completion.X p ≠ 0 :=
begin
  have h0 : (0 : FpX_int_completion p) = ⟨(0 : FpX_field_completion p), subring.zero_mem _⟩,
  { refl },
  rw [FpX_int_completion.X, ne.def, h0, subtype.mk_eq_mk, _root_.map_eq_zero],
  exact ratfunc.X_ne_zero,
end

lemma FpX_int_completion.X_coe_ne_zero :
  ¬(algebra_map (FpX_int_completion p) (𝓞 p K)) (FpX_int_completion.X p) = 0 :=
begin
  intro h,
  exact FpX_int_completion.X_ne_zero
    ((injective_iff_map_eq_zero _).mp (ring_of_integers.algebra_map_injective p K) _ h),
end

noncomputable! def open_unit_ball : height_one_spectrum (𝓞 p K) :=
{ as_ideal := 
  { carrier   := { x : 𝓞 p K | norm_on_K (x : K) < 1},
    add_mem'  := λ x y hx hy,
    begin
      rw [set.mem_set_of_eq, norm_on_K] at hx hy ⊢,
      refine lt_of_le_of_lt (spectral_norm_is_nonarchimedean 
        (algebra.is_algebraic_of_finite _ K) _ (x : K)
        (y : K)) (max_lt_iff.mpr ⟨hx, hy⟩),
        exact FpX_field_completion.norm_is_nonarchimedean,
    end,  
    zero_mem' := 
    begin
      rw [set.mem_set_of_eq, zero_mem_class.coe_zero, norm_on_K, spectral_norm_zero],
      exact zero_lt_one,
    end,
    smul_mem' := λ k x hx,
    begin
      rw [norm_on_K, smul_eq_mul, set.mem_set_of_eq, mul_mem_class.coe_mul,
        ← spectral_alg_norm_def (algebra.is_algebraic_of_finite 𝔽_[p]⟮⟮X⟯⟯ K)
          FpX_field_completion.norm_is_nonarchimedean,
        spectral_norm_is_mul (algebra.is_algebraic_of_finite 𝔽_[p]⟮⟮X⟯⟯ K) _ (k : K) (x : K)],
      exact mul_lt_one_of_nonneg_of_lt_one_right (norm_of_int_le_one k)
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
      rw [norm_on_K, ← spectral_alg_norm_def (algebra.is_algebraic_of_finite 𝔽_[p]⟮⟮X⟯⟯ K) 
        FpX_field_completion.norm_is_nonarchimedean, 
        spectral_norm_is_mul (algebra.is_algebraic_of_finite 𝔽_[p]⟮⟮X⟯⟯ K) 
        FpX_field_completion.norm_is_nonarchimedean] at hxy, 
      contrapose! hxy,
      exact one_le_mul_of_one_le_of_one_le hxy.1 hxy.2 }
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
      refine ⟨algebra_map _ _ (FpX_int_completion.X p), _, FpX_int_completion.X_coe_ne_zero K⟩,
      { have : ((algebra_map (FpX_int_completion p) (𝓞 p K)) (FpX_int_completion.X p) : K) =
        (algebra_map (FpX_field_completion p) K) (FpX_field_completion.X p),
        { refl },
        rw [norm_on_K, this, spectral_norm_extends], exact FpX_field_completion.norm_X_lt_one } }
  end }

def normalized_valuation (K : Type*) [field K] [eq_char_local_field p K] : valuation K ℤₘ₀ :=
(open_unit_ball K).valuation

@[priority 100] instance (K : Type*) [field K] [eq_char_local_field p K] : valued K ℤₘ₀ :=
  valued.mk' (normalized_valuation K)

instance : algebra (ratfunc 𝔽_[p]) K := algebra.comp (ratfunc 𝔽_[p]) 𝔽_[p]⟮⟮X⟯⟯ K

lemma normalized_valuation_X_ne_zero [eq_char_local_field p K] :
  (normalized_valuation K) (algebra_map (ratfunc 𝔽_[p]) _ X) ≠ 0 :=
by simp only [ne.def, _root_.map_eq_zero, ratfunc.X_ne_zero, not_false_iff]  


open multiplicative is_dedekind_domain.height_one_spectrum
def ramification_index (K : Type*) [field K] [eq_char_local_field p K] : ℤ := 
  -(with_zero.unzero (normalized_valuation_X_ne_zero K)).to_add

localized "notation (name := ramification_index)
  `e` := eq_char_local_field.ramification_index" in eq_char_local_field 

end eq_char_local_field

namespace FpX_field_completion

open eq_char_local_field
variable (p)

--fix
lemma FpX_int_completion.norm_lt_one_iff_dvd (f : 𝔽_[p]⟦X⟧) :
  ‖(f : 𝔽_[p]⟮⟮X⟯⟯)‖ < 1 ↔ ((FpX_int_completion.X p) ∣ f) := sorry
-- begin
--   have hf : ‖(f : 𝔽_[p]⟮⟮X⟯⟯)‖ = rank_one_valuation.norm_def (f : 𝔽_[p]⟮⟮X⟯⟯) := rfl,
--   rw [hf, height_one_spectrum.norm_lt_one_iff_val_lt_one],
--   rw height_one_spectrum.valued_adic_completion_def,

--   rw ← ideal.mem_span_singleton,

--   --rw ← height_one_spectrum.valuation_lt_one_iff_dvd, --not for completion
--   sorry
-- end
. 

-- set_option profiler true --7.26s ([FAE] 15.9 s on Jun8th)
-- Even compiling the statement is slow...
noncomputable! lemma open_unit_ball_def : (open_unit_ball 𝔽_[p]⟮⟮X⟯⟯).as_ideal =
  ideal.span {(algebra_map 𝔽_[p]⟦X⟧ (𝓞 p 𝔽_[p]⟮⟮X⟯⟯) (FpX_int_completion.X p))}
  /- ideal.span {(FpX_field_completion.ring_of_integers_equiv p).symm (FpX_int_completion.X p)} -/ := 
begin
  have hiff : ∀ (y : 𝔽_[p]⟮⟮X⟯⟯), y ∈ 𝓞 p 𝔽_[p]⟮⟮X⟯⟯ ↔ y ∈ 𝔽_[p]⟦X⟧, -- we should extract this to a lemma
  { intro y, rw mem_ring_of_integers,
    rw is_integrally_closed.is_integral_iff,
    refine ⟨λ h, _, λ h, ⟨⟨y, h⟩, rfl⟩⟩,
    { obtain ⟨x, hx⟩ := h,
      rw [← hx],
      exact x.2, }},
  simp only [open_unit_ball],
  ext ⟨x, hx⟩,
  have hx' : x = (⟨x, (hiff x).mp hx⟩ : 𝔽_[p]⟦X⟧) := rfl,
  rw [submodule.mem_mk, set.mem_set_of_eq, ideal.mem_span_singleton,
    norm_on_FpX_field_completion, set_like.coe_mk],
  conv_lhs {rw hx'},
  rw [FpX_int_completion.norm_lt_one_iff_dvd, dvd_iff_exists_eq_mul_left,
    dvd_iff_exists_eq_mul_left],
  refine ⟨λ h, _, λ h, _⟩,
  { obtain ⟨⟨c, hc⟩, hcx⟩ := h, 
    use algebra_map 𝔽_[p]⟦X⟧ _ ⟨c, hc⟩,
    rw [← map_mul, ← hcx],
    refl },
  { obtain ⟨⟨c, hc⟩, hcx⟩ := h, 
    use ⟨c, (hiff c).mp hc⟩,
    have h1 : FpX_int_completion.X p = ⟨FpX_field_completion.X p, X_mem_int_completion⟩ := rfl,
    rw [h1,mul_mem_class.mk_mul_mk, subtype.mk_eq_mk],
    have h2 : algebra_map 𝔽_[p]⟦X⟧ ↥(𝓞 p 𝔽_[p]⟮⟮X⟯⟯)(FpX_int_completion.X p) =
      ⟨FpX_field_completion.X p, (hiff _).mpr X_mem_int_completion⟩ := rfl,
    rw [h2, mul_mem_class.mk_mul_mk, subtype.mk_eq_mk] at hcx,
    exact hcx },
end 

variable {p}

.


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

section ring_of_integers

. 

open eq_char_local_field is_dedekind_domain.height_one_spectrum

--instance [eq_char_local_field p K] : valued K ℤₘ₀ := infer_instance

instance : is_rank_one (@eq_char_local_field.with_zero.valued p _ K _ _).v  := 
is_dedekind_domain.height_one_spectrum.valuation_is_rank_one K _


--TODO: Fix (can't find valued instance)
/- lemma eq_char_local_field.is_rank_one_hom_def :
  (is_rank_one.hom (@valued.v K _ ℤₘ₀ _ _)) =
  with_zero_mult_int_to_nnreal (valuation_base_ne_zero K (open_unit_ball K)) :=
sorry -/

.

--TODO: Is this needed?
--NOT TRUE (but eq. to a power is enough)
lemma function_extends_norm [eq_char_local_field p K] : 
  function_extends (norm : 𝔽_[p]⟮⟮X⟯⟯ → ℝ) (rank_one_valuation.mul_ring_norm_def K ℤₘ₀) :=
begin
  rw function_extends,
  intros x,
  simp only [rank_one_valuation.mul_ring_norm_def, rank_one_valuation.norm_def],
  change (((is_rank_one.hom valued.v) (valued.v ((algebra_map (FpX_field_completion p) K) x))) : ℝ)
    = ‖ x ‖,
  rw ←_root_.coe_nnnorm,
  rw nnreal.coe_eq,
  sorry
  /- rw eq_char_local_field.is_rank_one_hom_def,
  simp only [with_zero_mult_int_to_nnreal', with_zero_mult_int_to_nnreal_def', 
    monoid_with_zero_hom.coe_mk],
  by_cases hx : x = 0,
  { simp only [hx, map_zero, dif_pos, nnnorm_zero] },
  { rw dif_neg,
    sorry,
    sorry } -/
end

--fix
lemma ring_of_integers_eq_adic_completion_integers' [eq_char_local_field p K] :
  (𝓞 p K).to_subring = (@valued.v K _ ℤₘ₀ _ _).valuation_subring.to_subring :=
begin
sorry
{
  ext x,
  rw [subalgebra.mem_to_subring],
  rw eq_char_local_field.mem_ring_of_integers_iff_norm_le_one,
  simp only [valuation_subring.mem_to_subring, valuation.mem_valuation_subring_iff],
  rw ← is_dedekind_domain.height_one_spectrum.norm_le_one_iff_val_le_one,
  have hx : rank_one_valuation.norm_def x = norm_on_K x,
  { set N : mul_ring_norm K := rank_one_valuation.mul_ring_norm_def K ℤₘ₀ with hN,
    have hrfl: rank_one_valuation.norm_def x = N x := rfl,
    rw [hrfl, norm_on_K],
    apply spectral_norm_unique_field_norm_ext
      (algebra.is_algebraic_of_finite (FpX_field_completion p) K) function_extends_norm
      FpX_field_completion.norm_is_nonarchimedean },
  rw hx,
}
end


end ring_of_integers

--#lint