/-
Copyright (c) 2023 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import discrete_valuation_ring.extensions
import eq_characteristic.basic

noncomputable theory

open is_dedekind_domain nnreal polynomial ratfunc
open_locale eq_char_local_field nnreal discrete_valuation

variables (p : out_param (ℕ)) [fact (p.prime)] 

namespace eq_char_local_field

.

variables (K : Type*) [field K] [eq_char_local_field p K]

-- TODO: come back after fixing the names in `dvr.extensions`

-- NOTE: There is a diamond on 𝔽_[p]⟮⟮X⟯⟯, but by setting this priority lower, it seems
-- that Lean finds the correct instance.
@[priority 100] instance : valued K ℤₘ₀ := valued.mk' (w 𝔽_[p]⟮⟮X⟯⟯ K)

instance : valuation.is_discrete 
  (eq_char_local_field.with_zero.valued p K).v := 
is_discrete_of_finite 𝔽_[p]⟮⟮X⟯⟯ K

-- Without the `by apply`, it times out
instance : discrete_valuation_ring (𝓞 p K) :=
by apply dvr_of_finite_extension 𝔽_[p]⟮⟮X⟯⟯ K


end eq_char_local_field

namespace FpX_field_completion

noncomputable! instance : is_rank_one (@FpX_field_completion.with_zero.valued p _).v :=
sorry

instance : normed_field 𝔽_[p]⟮⟮X⟯⟯ := rank_one_valuation.valued_field.to_normed_field _ _

noncomputable! lemma residue_field_card_eq_char :
  nat.card (local_ring.residue_field 𝔽_[p]⟦X⟧) = p :=
begin
  rw FpX_int_completion,
  sorry
end

open is_dedekind_domain is_dedekind_domain.height_one_spectrum


variable (p)
def X := algebra_map 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯ (FpX_int_completion.X p)

lemma X_eq_coe : X p = ↑(@ratfunc.X 𝔽_[p] _ _) := rfl

variable {p}

lemma norm_X : ‖ X p ‖ = 1/(p : ℝ) :=
begin
  sorry
  /- have hv : valued.v (X p) = multiplicative.of_add (-1 : ℤ),
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
  { simp only [with_zero.coe_ne_zero, with_zero_mult_int_to_nnreal_strict_mono, not_false_iff] } -/
end

lemma norm_X_pos : 0 < ‖ X p ‖ :=
by rw [norm_X, one_div, inv_pos, nat.cast_pos]; exact (_inst_1.out).pos

lemma norm_X_lt_one : ‖ X p ‖ < 1 :=
by rw [norm_X, one_div]; exact inv_lt_one (nat.one_lt_cast.mpr (_inst_1.out).one_lt)

lemma X_mem_int_completion : X p ∈ FpX_int_completion p :=
begin
  rw [mem_FpX_int_completion, ← norm_le_one_iff_val_le_one],
  sorry --exact le_of_lt norm_X_lt_one, 
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

--TODO: Filippo, do we still need this?
--`[FAE]` The following `instance` will probably be PR'd soon in greater generality for all
-- integrally closed domains: see 
-- [https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/.E2.9C.94.20gcd_monoid]
noncomputable! instance  : normalized_gcd_monoid 𝔽_[p]⟦X⟧  :=
sorry

lemma FpX_int_completion.X_ne_zero : FpX_int_completion.X p ≠ 0 :=
begin
  have h0 : (0 : FpX_int_completion p) = ⟨(0 : FpX_field_completion p), subring.zero_mem _⟩,
  { refl },
  rw [FpX_int_completion.X, ne.def, h0, subtype.mk_eq_mk, _root_.map_eq_zero],
  exact ratfunc.X_ne_zero,
end

variables (K : Type*) [field K] [eq_char_local_field p K]

lemma FpX_int_completion.X_coe_ne_zero :
  ¬(algebra_map (FpX_int_completion p) (𝓞 p K)) (FpX_int_completion.X p) = 0 :=
begin
  sorry/- intro h,
  exact FpX_int_completion.X_ne_zero
    ((injective_iff_map_eq_zero _).mp (ring_of_integers.algebra_map_injective p K) _ h), -/
end

--TODO: move
instance : algebra (ratfunc 𝔽_[p]) K := algebra.comp (ratfunc 𝔽_[p]) 𝔽_[p]⟮⟮X⟯⟯ K


end FpX_int_completion

#exit




variables {K : Type*} [field K] [eq_char_local_field p K]

namespace eq_char_local_field

def norm_on_K : K → ℝ := disc_norm_extension (algebra.is_algebraic_of_finite 𝔽_[p]⟮⟮X⟯⟯ K)

--def norm_on_K : K → ℝ := spectral_norm 𝔽_[p]⟮⟮X⟯⟯ K

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
    int_polynomial' (polynomial 𝔽_[p]) (ratfunc 𝔽_[p]) (ideal_X 𝔽_[p]) hx with hP,
    rw [mem_ring_of_integers, is_integral, adic_algebra.int_algebra_map_def,
      ring_hom.is_integral_elem],
    use P,
    split,
    --TODO: extract general lemmas for int_polynomial'
    { rw [monic, subtype.ext_iff, subring.coe_one, int_polynomial'_leading_coeff_eq],
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

.


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

--#lint