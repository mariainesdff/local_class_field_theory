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


namespace eq_char_local_field

.

variables (p : out_param (ℕ)) [hp : fact (p.prime)] 

include hp
variables (K : Type*) [field K] [eq_char_local_field p K]

-- TODO: come back after fixing the names in `dvr.extensions`

--TODO: How can I put this inside the proof of `valued`?
def foo : normed_field K := extension_normed_field 𝔽_[p]⟮⟮X⟯⟯ K

local attribute [instance] foo

-- NOTE: There is a diamond on 𝔽_[p]⟮⟮X⟯⟯, but by setting this priority lower, it seems
-- that Lean finds the correct instance.
@[priority 100] instance : valued K ℤₘ₀ := --valued.mk' (w 𝔽_[p]⟮⟮X⟯⟯ K)
{ v := w 𝔽_[p]⟮⟮X⟯⟯ K,
  is_topological_valuation := λ U,
  begin
    rw metric.mem_nhds_iff,
    refine ⟨λ h, _, λ h, _⟩, 
    { obtain ⟨ε, hε, h⟩ := h,
      sorry
      /- use units.mk0 ⟨ε, le_of_lt hε⟩ (ne_of_gt hε),
      intros x hx,
      exact h (mem_ball_zero_iff.mpr hx)  -/},
    { obtain ⟨ε, hε⟩ := h,
      sorry
      /- use [(ε : ℝ), nnreal.coe_pos.mpr (units.zero_lt _)],
      intros x hx,
      exact hε  (mem_ball_zero_iff.mp hx) -/ },

    /- rw metric.mem_nhds_iff,
    refine ⟨λ h, _, λ h, _⟩, 
    { obtain ⟨ε, hε, h⟩ := h,
      use units.mk0 ⟨ε, le_of_lt hε⟩ (ne_of_gt hε),
      intros x hx,
      exact h (mem_ball_zero_iff.mpr hx) },
    { obtain ⟨ε, hε⟩ := h,
      use [(ε : ℝ), nnreal.coe_pos.mpr (units.zero_lt _)],
      intros x hx,
      exact hε  (mem_ball_zero_iff.mp hx) }, -/
  end,
  ..(uniform_space_extension (algebra.is_algebraic_of_finite 𝔽_[p]⟮⟮X⟯⟯ K)),
  ..non_unital_normed_ring.to_normed_add_comm_group }

local attribute [-instance] foo

--TODO: FIX!

instance : complete_space K := extension_complete 𝔽_[p]⟮⟮X⟯⟯ K

instance : valuation.is_discrete (eq_char_local_field.with_zero.valued p K).v := 
is_discrete_of_finite 𝔽_[p]⟮⟮X⟯⟯ K

-- Without the `by apply`, it times out
instance : discrete_valuation_ring (𝓞 p K) := by apply dvr_of_finite_extension 𝔽_[p]⟮⟮X⟯⟯ K

end eq_char_local_field


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