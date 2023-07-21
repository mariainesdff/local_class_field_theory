/-
Copyright (c) 2023 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import analysis.specific_limits.basic
import discrete_valuation_ring.complete
import number_theory.padics.padic_integers
import ring_theory.dedekind_domain.adic_valuation
import for_mathlib.ring_theory.dedekind_domain.ideal

--import for_mathlib.laurent_series_iso.old_power_series_adic_completion
--set_option profiler true

noncomputable theory

open is_dedekind_domain is_dedekind_domain.height_one_spectrum nnreal polynomial valuation 
  normalization_monoid multiplicative
open_locale nnreal discrete_valuation

def int.p_height_one_ideal (p : out_param ℕ) [hp : fact (p.prime)] : 
  height_one_spectrum ℤ :=
{ as_ideal := ideal.span{(p : ℤ)},
  is_prime := by { rw ideal.span_singleton_prime, 
    exacts [nat.prime_iff_prime_int.mp hp.1, nat.cast_ne_zero.mpr hp.1.ne_zero] },
  ne_bot   := by {simp only [ne.def, ideal.span_singleton_eq_bot, nat.cast_eq_zero],
    exact hp.1.ne_zero, }}
open int

open unique_factorization_monoid

open_locale classical

namespace padic_comparison

open padic

variables (p : out_param ℕ) [fact (p.prime)]
  
local attribute [-instance] rat.metric_space rat.normed_field rat.densely_normed_field
  /- rat.normed_linear_ordered_field -/  rat.division_ring rat.normed_add_comm_group

instance : separated_space ℚ_[p] := metric_space.to_separated

def padic_valued : valued ℚ ℤₘ₀ := (p_height_one_ideal p).adic_valued

local attribute [instance] padic_valued

lemma padic_norm_of_int_eq_val_norm (x : ℤ) : ((padic_norm p x) : ℝ) =
  with_zero_mult_int_to_nnreal (ne_zero.ne p) (valued.v (x : ℚ)) := 
begin
  classical,
  by_cases hx : x = 0,
  { simp only [hx, padic_norm.zero, algebra_map.coe_zero, _root_.map_zero] },
  { have hx0 : ¬(x : ℚ) = 0 := cast_ne_zero.mpr hx,
    have hv0 : valued.v (x : ℚ) ≠ (0 : ℤₘ₀),
    { rw [ne.def, zero_iff], exact hx0 },
    have heq : multiplicative.of_add (-(associates.mk (p_height_one_ideal p).as_ideal).count 
      (associates.mk (ideal.span {x} : ideal ℤ)).factors : ℤ) = (with_zero.unzero hv0),
    { erw [← with_zero.coe_inj, ← int_valuation_def_if_neg _ hx, with_zero.coe_unzero, 
        valuation_of_algebra_map], refl, },
    have hx' : (ideal.span {x} : ideal ℤ) ≠ 0,
    { rwa [ideal.zero_eq_bot, ne.def, ideal.span_singleton_eq_bot] },
    have hp : prime (p : ℤ),
    { exact nat.prime_iff_prime_int.mp _inst_1.1 },
    have hp' : (ideal.span {(p : ℤ)} : ideal ℤ).is_prime,
    { rwa ideal.span_singleton_prime (ne_zero.ne (p : ℤ)), },
    have hpne : (ideal.span {(p : ℤ)} : ideal ℤ) ≠ ⊥,
    { rw [ne.def, ideal.span_singleton_eq_bot], exact ne_zero.ne (p : ℤ) }, 
    simp only [padic_norm.eq_zpow_of_nonzero hx0, with_zero_mult_int_to_nnreal, 
      with_zero_mult_int_to_nnreal_def, zero_iff,
      rat.cast_zpow, rat.cast_coe_nat, monoid_with_zero_hom.coe_mk, dif_neg hx0, coe_zpow, 
      nnreal.coe_nat_cast],
    apply congr_arg,
    rw [← heq, padic_val_rat.of_int_multiplicity (nat.prime.ne_one _inst_1.1) hx,
      to_add_of_add, neg_inj, nat.cast_inj, ← part_enat.coe_inj, part_enat.coe_get,
      multiplicity_eq_count_normalized_factors hp.irreducible hx, int.normalize_coe_nat,
      part_enat.coe_inj, count_normalized_factors_eq_count_normalized_factors_span hx (ne_zero.ne p) rfl hp, count_normalized_factors_eq_associates_count hx' hp' hpne],
    refl },
end

lemma padic_norm_eq_val_norm (z : ℚ) : ((padic_norm p z) : ℝ) =
  with_zero_mult_int_to_nnreal (ne_zero.ne p) (valued.v z) := 
begin
  by_cases hz : z = 0,
  { simp only [hz, padic_norm.zero, algebra_map.coe_zero, _root_.map_zero] },
  { obtain ⟨x, y, hxy⟩ := is_localization.mk'_surjective (non_zero_divisors ℤ) z,
    have hz : is_localization.mk' ℚ x y = x/y,
    { simp only [is_fraction_ring.mk'_eq_div, eq_int_cast, _root_.coe_coe] },
    erw [← hxy, valuation_of_mk', hz, padic_norm.div,_root_.coe_coe, rat.cast_div, map_div₀, 
      nonneg.coe_div],
    apply congr_arg2;
    { convert padic_norm_of_int_eq_val_norm p _, erw valuation_of_algebra_map }},
end

lemma uniform_inducing_coe : uniform_inducing (coe : ℚ → ℚ_[p]) :=
begin
  have hp_one : (1 : ℝ≥0) < p := nat.one_lt_cast.mpr (nat.prime.one_lt (fact.out _)),
  apply uniform_inducing.mk',
  simp_rw @metric.mem_uniformity_dist ℚ_[p] _ _,
  refine (λ S, ⟨λ hS, _, _⟩),
  { obtain ⟨m, ⟨-, hM_sub⟩⟩ := (valued.has_basis_uniformity ℚ ℤₘ₀).mem_iff.mp hS,
    set M := (with_zero_mult_int_to_nnreal (ne_zero.ne p) m.1).1 with hM,
    refine ⟨{p : ℚ_[p] × ℚ_[p] | dist p.1 p.2 < M}, ⟨⟨M, ⟨_, λ a b h, h⟩⟩, λ x y h, _⟩⟩,
    { exact with_zero_mult_int_to_nnreal_pos _ (is_unit_iff_ne_zero.mp (units.is_unit m)) },
    { apply hM_sub,
      simp only [set.mem_set_of_eq, dist] at h ⊢,
      rwa [← padic.coe_sub, padic_norm_e.eq_padic_norm', padic_norm_eq_val_norm, hM,
        units.val_eq_coe, val_eq_coe, nnreal.coe_lt_coe,
        (with_zero_mult_int_to_nnreal_strict_mono hp_one).lt_iff_lt,
        ← neg_sub, valuation.map_neg] at h }},
  { rw (valued.has_basis_uniformity ℚ ℤₘ₀).mem_iff,
    rintros ⟨T, ⟨ε, ⟨hε, H⟩⟩, h⟩,
    obtain ⟨M, hM⟩ := (real.exists_strict_mono_lt (with_zero_mult_int_to_nnreal_strict_mono
      hp_one) hε),
    { refine ⟨M, by triv, λ q hq, _⟩,
      simp only [set.mem_set_of_eq, dist] at H hq,
      have : (↑q.fst, ↑q.snd) ∈ T,
      { apply H,
        rw [← padic.coe_sub, padic_norm_e.eq_padic_norm', padic_norm_eq_val_norm, ← neg_sub,
          valuation.map_neg],
        exact (nnreal.coe_lt_coe.mpr
          ((with_zero_mult_int_to_nnreal_strict_mono hp_one).lt_iff_lt.mpr hq)).trans hM,},
      specialize h q.1 q.2 this,
      rwa prod.mk.eta at h }},
end

lemma dense_coe : dense_range  (coe : ℚ → ℚ_[p]) := metric.dense_range_iff.mpr (padic.rat_dense p)

def padic_pkg : abstract_completion ℚ :=
{ space            := ℚ_[p],
  coe              := coe,
  uniform_struct   := infer_instance,
  complete         := infer_instance,
  separation       := infer_instance,
  uniform_inducing := uniform_inducing_coe p,
  dense            := dense_coe p }


def coe_ring_hom : ℚ →+* ℚ_[p] :=
{ to_fun    := (padic_pkg p).2,
  map_one'  := rat.cast_one,
  map_mul'  := rat.cast_mul,
  map_zero' := rat.cast_zero,
  map_add'  := rat.cast_add }

namespace padic'

--`toDO`  do we really need to remove it?
-- local attribute [- instance] rat.cast_coe

@[reducible]
def Q_p : Type* := adic_completion ℚ (p_height_one_ideal p)

instance : is_discrete (@valued.v (Q_p p) _ ℤₘ₀ _ _) := 
completion.is_discrete _ _ _

instance : normed_field (Q_p p) := rank_one_valuation.valued_field.to_normed_field (Q_p p) ℤₘ₀

def padic'_pkg : abstract_completion ℚ :=
{ space            := Q_p p,
  coe              := coe,
/-This `coe` is not the coercion from `ℚ` to every field of characteristic zero, but rather the
coercion from a space to its uniform completion-/
  uniform_struct   := infer_instance,
  complete         := infer_instance,
  separation       := infer_instance,
  uniform_inducing := (uniform_space.completion.uniform_embedding_coe ℚ).1,
  dense            := uniform_space.completion.dense_range_coe }

end padic'

open padic'

def compare : Q_p p ≃ᵤ ℚ_[p] :=
abstract_completion.compare_equiv (padic'_pkg p) (padic_pkg p)

/-`extension_as_ring_hom_to_fun` and its siblings might be redundant-/

lemma uniform_continuous_coe : uniform_continuous (coe : ℚ → ℚ_[p]) :=
(uniform_inducing_iff'.1 (uniform_inducing_coe p)).1


definition extension_as_ring_hom : Q_p p →+* ℚ_[p] := 
uniform_space.completion.extension_hom (coe_ring_hom p) (uniform_continuous_coe p).continuous


@[simp]
lemma extension_as_ring_hom_to_fun : (extension_as_ring_hom p).to_fun =
  uniform_space.completion.extension (coe : ℚ → ℚ_[p]) := rfl


lemma extension_eq_compare : (extension_as_ring_hom p).to_fun = (compare p).to_fun :=
begin
  simp only [extension_as_ring_hom_to_fun, equiv.to_fun_as_coe, uniform_equiv.coe_to_equiv],
  apply uniform_space.completion.extension_unique (uniform_continuous_coe p)
    ((padic'_pkg p).uniform_continuous_compare_equiv (padic_pkg p)),
  intro a,
  have : (padic_pkg p).coe a = (↑a : ℚ_[p]) := rfl,
  rw [← this, ← abstract_completion.compare_coe],
  refl,
end

definition padic_equiv : (Q_p p) ≃+* ℚ_[p] :=
{ map_mul' := by {rw ← extension_eq_compare p, use (extension_as_ring_hom p).map_mul'},
  map_add' := by {rw ← extension_eq_compare p, exact (extension_as_ring_hom p).map_add'},
  ..(compare p) }

instance : char_zero (Q_p p) := (padic_equiv p).to_ring_hom.char_zero

@[reducible]
def Z_p := (@valued.v (Q_p p) _ ℤₘ₀ _ _).valuation_subring

lemma exists_mem_le_one_of_lt_one {x : (Q_p p)} (hx : valued.v x ≤ (1 : ℤₘ₀)) : ∃ (y : Z_p p),
  (y : (Q_p p)) = x ∧ (valued.v (y : Q_p p)) = valued.v x :=
begin
  have hv := valued.v.is_equiv_valuation_valuation_subring,
  have := valuation_subring.mem_of_valuation_le_one (Z_p p) x _,
  use ⟨x, this⟩,
  simp only [set_like.coe_mk, eq_self_iff_true, and_self],
  exact ((valuation.is_equiv_iff_val_le_one _ _).mp hv).mp hx,
end

lemma exists_mem_lt_one_of_lt_one {x : (Q_p p)} (hx : valued.v x < (1 : ℤₘ₀)) : ∃ (y : Z_p p),
  (y : (Q_p p)) = x ∧ (valued.v (y : Q_p p)) = valued.v x :=
begin
  have hv := valued.v.is_equiv_valuation_valuation_subring,
  have := valuation_subring.mem_of_valuation_le_one (Z_p p) x (le_of_lt _),
  use ⟨x, this⟩,
  simp only [set_like.coe_mk, eq_self_iff_true, and_self],
  exact ((valuation.is_equiv_iff_val_lt_one _ _).mp hv).mp hx,
end

-- TODO: slow
/-- TODO: possible diamond here (the proof for ℤ_[p] does not translate) -/
instance : char_zero (Z_p p) := 
{ cast_injective := λ m n h, 
  begin
    simp only [subtype.ext_iff, subring.coe_nat_cast, nat.cast_inj] at h,
    exact h
  end }

def padic'_int.height_one_ideal (p : out_param ℕ) [hp : fact (p.prime)] : 
  height_one_spectrum (Z_p p) :=
{ as_ideal := local_ring.maximal_ideal (Z_p p),
  is_prime := ideal.is_maximal.is_prime (local_ring.maximal_ideal.is_maximal _),
  ne_bot   := begin
    rw [ne.def, ← local_ring.is_field_iff_maximal_ideal_eq],
    exact discrete_valuation.not_is_field _
  end }

instance : valued (Q_p p) ℤₘ₀ := height_one_spectrum.valued_adic_completion ℚ (p_height_one_ideal p)


/- The lemma `padic_int_ring_equiv_mem` states that an element `x ∈ ℚ_[p]` is in `ℤ_[p]` if and
only if it is in the image of `Z_p p` via the ring equivalence `padic_equiv p`. See
`padic_int_ring_equiv` for an upgrade of this statement to a ring equivalence `Z_p p ≃+* ℤ_[p]`-/

def padic_int.valuation_subring : valuation_subring ℚ_[p] :=
{ to_subring := padic_int.subring p,
  mem_or_inv_mem' :=
begin
  have not_field : ¬ is_field ℤ_[p] := (discrete_valuation_ring.not_is_field _),
-- Marking `not_field` as a separate assumption makes the computation faster
  have := ((discrete_valuation_ring.tfae ℤ_[p] not_field).out 0 1).mp
    padic_int.discrete_valuation_ring,
  intro x,
  rcases (valuation_ring.iff_is_integer_or_is_integer ℤ_[p] ℚ_[p]).mp this x with hx | hx,
  { apply or.intro_left,
    obtain ⟨y, hy⟩ := hx,
    rw ← hy,
    simp only [padic_int.algebra_map_apply, subring.mem_carrier, padic_int.mem_subring_iff,
      padic_int.padic_norm_e_of_padic_int],
    apply padic_int.norm_le_one },
  { apply or.intro_right,
    obtain ⟨y, hy⟩ := hx,
    rw ← hy,
    simp only [padic_int.algebra_map_apply, subring.mem_carrier, padic_int.mem_subring_iff,
      padic_int.padic_norm_e_of_padic_int],
    apply padic_int.norm_le_one,
    },
end }
 
open filter
open_locale filter topology

@[reducible]
def comap_Zp : valuation_subring ℚ_[p] :=
valuation_subring.comap (Z_p p) (padic_equiv p).symm.to_ring_hom

-- TODO: Ask on Zulip if it exists and move it to another file/folder
-- **FAE** This is in lean4 already
lemma nnreal.lt_one_of_tendsto_pow_0 (a : ℝ≥0) (h : tendsto (λ n : ℕ, a^n) at_top (𝓝 0)) :
  a < 1 :=
begin
  by_cases ha₀ : a = 0,
  {rw ha₀, exact zero_lt_one,},
  { by_contradiction ha_le,
    rw not_lt at ha_le,
    by_cases ha : a = 1,
    { simp only [ha, one_pow] at h,
      exact zero_ne_one (tendsto_nhds_unique h tendsto_const_nhds) },
    { replace h : tendsto (λ n : ℕ, (a : ennreal) ^n) at_top (𝓝 0),
      { rw ← ennreal.coe_zero,
        simp_rw [← ennreal.coe_pow, ennreal.tendsto_coe],
        exact h, },
      set b : ennreal := ↑(a⁻¹) with hb,
      replace h : tendsto (λ n : ℕ, b ^ n) at_top (𝓝 ⊤),
      { rw [hb, ennreal.coe_inv ha₀],
        convert (@ennreal.tendsto_inv_iff ℕ at_top (λ n, (↑a) ^ n) 0).mpr h,
        { funext n, exact ennreal.inv_pow.symm, },
        { simp only [ennreal.inv_zero] }},
      have hb₁ : b < 1,
      { rw [hb, ← ennreal.coe_one, ennreal.coe_lt_coe],
        exact inv_lt_one (lt_of_le_of_ne ha_le (ne.symm ha)) },
      exact ennreal.zero_ne_top (tendsto_nhds_unique
        (ennreal.tendsto_pow_at_top_nhds_0_of_lt_1 hb₁) h)}},
  end


/-The two lemmas below have basically the same proof, except from the fact that in one we
 use that `x : ℚ_[p]` satisfies ‖ x ‖ < 1 iff `p ∣ x` and in the other that `x : (Q_p p)` has
 ‖ x ‖ < 1 iff it belongs to the maximal ideal...-/
lemma padic_int.nonunit_mem_iff_top_nilpotent (x : ℚ_[p]) :
  x ∈ (padic_int.valuation_subring p).nonunits ↔ filter.tendsto (λ n : ℕ, x ^ n) at_top (𝓝 0) :=
begin
  have aux : ∀ n : ℕ, ‖ x^n ‖ = ‖ x ‖ ^ n,
  { exact λ n, norm_pow _ n},
  rw [tendsto_zero_iff_norm_tendsto_zero, filter.tendsto_congr aux],
  refine ⟨λ H, _, λ H, _⟩,
  { obtain ⟨h1, h2⟩ := valuation_subring.mem_nonunits_iff_exists_mem_maximal_ideal.mp H,
    exact _root_.tendsto_pow_at_top_nhds_0_of_lt_1 (norm_nonneg _)
       (padic_int.mem_nonunits.mp $ (local_ring.mem_maximal_ideal _).mp h2) },
  { have : ‖ x ‖ < 1,
    { suffices : (⟨‖ x ‖, norm_nonneg _⟩ : ℝ≥0) < 1,
      { rwa [← nnreal.coe_lt_coe, nnreal.coe_one, ← subtype.val_eq_coe] at this },
      apply nnreal.lt_one_of_tendsto_pow_0,
      rwa [← nnreal.tendsto_coe, nnreal.coe_zero] },
    apply valuation_subring.mem_nonunits_iff_exists_mem_maximal_ideal.mpr,
    exact ⟨(padic_int.mem_subring_iff p).mpr (le_of_lt this), (local_ring.mem_maximal_ideal _).mpr
      (padic_int.mem_nonunits.mpr this)⟩ },
end


--The lemma below could probably be incorporated in the proof of 
-- `unit_ball.nonunit_mem_iff_top_nilpotent` if the whole things does not become too long
lemma go_faster {x : (Q_p p)} (h_go : ‖ x ‖ < 1) (H : tendsto (λ (n : ℕ), ‖x‖ ^ n) at_top (𝓝 0)) :
  x ∈ (Z_p p).nonunits :=
begin
  apply valuation_subring.mem_nonunits_iff_exists_mem_maximal_ideal.mpr,
  have : ‖ x ‖ < 1,
    { suffices : (⟨‖ x ‖, norm_nonneg _⟩ : ℝ≥0) < 1,
      { rwa [← nnreal.coe_lt_coe, nnreal.coe_one, ← subtype.val_eq_coe] at this },
      apply nnreal.lt_one_of_tendsto_pow_0,
      rwa [← nnreal.tendsto_coe, nnreal.coe_zero] },
    replace this : valued.v x < (1 : ℤₘ₀),
    { apply (rank_one_valuation.norm_lt_one_iff_val_lt_one x).mp this },
    obtain ⟨y, hy₁, hy₂⟩ := exists_mem_lt_one_of_lt_one p this,
    rw [← hy₂] at this,
    have this' := this,
    rw [← completion.valuation.adic_of_compl_eq_compl_of_adic ℤ (p_height_one_ideal p) ℚ (↑y)] at this,
    let M := (completion.max_ideal_of_completion) ℤ (p_height_one_ideal p) ℚ,
    have v_lt_one := @is_dedekind_domain.height_one_spectrum.valuation_lt_one_iff_dvd (Z_p p) _ _ _ (Q_p p)
      _ _ _ (completion.max_ideal_of_completion ℤ (p_height_one_ideal p) ℚ) y,
    have eq_y : (algebra_map ↥(Z_p p) (Q_p p)) y = (↑y : (Q_p p)) := rfl,
    rw eq_y at v_lt_one,
    rw [v_lt_one] at this,
    simp only [ideal.dvd_span_singleton, mem_nonunits_iff, valuation_subring.algebra_map_apply,
      set_like.coe_mk, forall_true_left] at this,--squeeze_simp has a bizarre *unwanted* effect
    rw [← hy₁],
    simp only [mem_valuation_subring_iff, set_like.eta, exists_prop],
    exact ⟨le_of_lt this', this⟩,--this final `exact` probably shows that having both `this'` and `this` is perfectly useless
end

lemma unit_ball.nonunit_mem_iff_top_nilpotent (x : (Q_p p)) :
  x ∈ (Z_p p).nonunits ↔ filter.tendsto (λ n : ℕ, x ^ n) at_top (𝓝 0) :=
begin
  have h_max_ideal : (padic'_int.height_one_ideal p).as_ideal =
    (local_ring.maximal_ideal ↥(Z_p p)) := rfl,
  have aux : ∀ n : ℕ, ‖ x^n ‖ = ‖ x ‖ ^ n,
  { exact λ n, norm_pow _ n},
  rw [tendsto_zero_iff_norm_tendsto_zero, filter.tendsto_congr aux],
  refine ⟨λ H, _, λ H, _⟩,
  { simp_rw norm_pow,
    obtain ⟨h, x_mem⟩ := valuation_subring.mem_nonunits_iff_exists_mem_maximal_ideal.mp H,
    have := (@valuation_lt_one_iff_dvd (Z_p p) _ _ _ (Q_p p) _ _ _ (padic'_int.height_one_ideal p)
      ⟨x, h⟩).mpr,
    simp only [h_max_ideal, ideal.dvd_span_singleton, mem_nonunits_iff,
      valuation_subring.algebra_map_apply, set_like.coe_mk, x_mem, forall_true_left] at this,
    replace this : valued.v x < (1 : ℤₘ₀),
    { convert this using 1,
      exact (completion.valuation.adic_of_compl_eq_compl_of_adic ℤ
        (int.p_height_one_ideal p) ℚ x).symm },
      exact _root_.tendsto_pow_at_top_nhds_0_of_lt_1 (norm_nonneg _)
      ((rank_one_valuation.norm_lt_one_iff_val_lt_one _ ).mpr this), },
  { have : ‖ x ‖ < 1,
    { suffices : (⟨‖ x ‖, norm_nonneg _⟩ : ℝ≥0) < 1,
      { rwa [← nnreal.coe_lt_coe, nnreal.coe_one, ← subtype.val_eq_coe] at this },
      apply nnreal.lt_one_of_tendsto_pow_0,
      rwa [← nnreal.tendsto_coe, nnreal.coe_zero] },
      apply go_faster p this H }
end


lemma mem_nonunits_iff (x : (Q_p p)) :
  x ∈ (Z_p p).nonunits ↔ (padic_equiv p) x ∈ (comap_Zp p).nonunits :=
begin
  let φ : (Z_p p) ≃+* (comap_Zp p),
  { have :=  (Z_p p).to_subring.comap_equiv_eq_map_symm (padic_equiv p).symm,
    replace this := ring_equiv.subring_congr this.symm,
    use (@ring_equiv.subring_map _ _ _ _  (Z_p p).to_subring (padic_equiv p)).trans this, },
  refine ⟨λ hx, _, λ hx, _⟩,
  all_goals { rw valuation_subring.mem_nonunits_iff_exists_mem_maximal_ideal at hx,
    rw valuation_subring.mem_nonunits_iff_exists_mem_maximal_ideal},
    { refine ⟨_, map_nonunit (↑φ : ((Z_p p) →+* (comap_Zp p))) _ hx.some_spec⟩ },
    { rcases hx with ⟨h1, h2⟩,
      have h3 := valuation_subring.mem_comap.mp h1,
      have : ((padic_equiv p).symm.to_ring_hom) ((padic_equiv p) x) = 
        ((padic_equiv p).symm.to_ring_hom) ((padic_equiv p).to_ring_hom x) := rfl,
      simp_rw [this, ← ring_hom.comp_apply,
        ring_equiv.symm_to_ring_hom_comp_to_ring_hom, ring_hom.id_apply] at h3,
      have h4 : (φ.symm) (⟨(padic_equiv p) x, h1⟩ : {z // z ∈ comap_Zp p}) = ⟨x, h3⟩,
      { set b : ℚ_[p] := φ ⟨x, h3⟩ with hb,
        have : b = (padic_equiv p) x := rfl,
        simp_rw [← this, hb, set_like.eta, ring_equiv.symm_apply_apply], },
      replace h2 := map_nonunit (↑φ.symm : ((comap_Zp p) →+* (Z_p p))) _ h2,
      erw h4 at h2,
      refine ⟨_, h2⟩ },
end

lemma valuation_subrings_eq : padic_int.valuation_subring p = comap_Zp p :=
begin
  rw ← valuation_subring.nonunits_inj,
  ext x,
  refine ⟨λ hx, _, λ hx, _⟩,
  { rw [← (padic_equiv p).apply_symm_apply x], 
    rw [← mem_nonunits_iff, 
      unit_ball.nonunit_mem_iff_top_nilpotent, ← _root_.map_zero (padic_equiv p).symm],
    simp_rw [← _root_.map_pow (padic_equiv p).symm],
    apply (@continuous.continuous_at _ _ _ _ _ 0 (compare p).3.continuous).tendsto.comp,
    rwa ← padic_int.nonunit_mem_iff_top_nilpotent },
  { rw [←  (padic_equiv p).apply_symm_apply x, ← mem_nonunits_iff, 
      unit_ball.nonunit_mem_iff_top_nilpotent] at hx,
    replace hx := @tendsto.comp ℕ (Q_p p) ℚ_[p] (λ n, ((padic_equiv p).symm x) ^ n) (padic_equiv p)
      at_top (𝓝 0) (𝓝 0) _ hx,
    -- We postpone the verification of the first assumption in `tendsto.comp`
    { simp_rw [← _root_.map_pow (padic_equiv p).symm x, function.comp, ring_equiv.apply_symm_apply]
      at hx,
      rwa padic_int.nonunit_mem_iff_top_nilpotent },
    { rw [← _root_.map_zero (padic_equiv p)],
      apply continuous.tendsto (compare p).symm.3.continuous 0}},
end

instance : algebra ℚ_[p] (Q_p p) := 
ring_hom.to_algebra (padic_comparison.padic_equiv p).symm

instance : is_scalar_tower ℚ ℚ_[p] (Q_p p) := 
{ smul_assoc := λ r x y, begin
    simp only [algebra.smul_def, eq_rat_cast, _root_.map_mul, map_rat_cast, mul_assoc],
    refl,
  end  }

lemma padic_valued_valuation_p : 
  @valued.v ℚ _ ℤₘ₀ _ (padic_valued p) (p : ℚ) = (of_add (-1 : ℤ)) := 
begin
  have hp : (p : ℚ) = algebra_map ℤ ℚ (p : ℤ) := rfl,
  rw [adic_valued_apply, hp, valuation_of_algebra_map, fae_int_valuation_apply, 
    int_valuation_def_if_neg (p_height_one_ideal p) 
      (nat.cast_ne_zero.mpr (nat.prime.ne_zero _inst_1.1))],
  congr,
  apply associates.count_self,
  rw associates.irreducible_mk,
  apply prime.irreducible,
  exact ideal.prime_of_is_prime ( ideal.span_singleton_eq_bot.mp.mt (nat.cast_ne_zero.mpr 
    (nat.prime.ne_zero _inst_1.1))) (ideal.is_maximal.is_prime' (p_height_one_ideal p).as_ideal)
end

lemma padic'.coe_eq (x : ℚ) : (x : Q_p p) = (((padic'_pkg p).coe x) : (padic'_pkg p).space) :=
begin
  have hp : (x : Q_p p) = (padic_pkg p).compare (padic'_pkg p) (x : ℚ_[p]),
  { have h: (padic_pkg p).compare (padic'_pkg p) (x : ℚ_[p]) = algebra_map ℚ_[p] (Q_p p) x := rfl,
    rw [h, map_rat_cast] },
  rw [← abstract_completion.compare_coe (padic_pkg p) (padic'_pkg p), hp],
  refl,
end

lemma padic'.valuation_p : 
   valued.v (p : Q_p p) = (of_add (-1 : ℤ)) := 
begin
   letI : valued ℚ ℤₘ₀ := padic_valued p,
   have hp : (p : Q_p p) = (((coe : ℚ → (Q_p p)) p) : Q_p p),
   { have : ∀ x : ℚ, (coe : ℚ → (Q_p p)) x = (x : Q_p p),
     { intro x, rw padic'.coe_eq, refl, },
     rw this, simp only [rat.cast_coe_nat], },
   rw [hp, valued.valued_completion_apply (p : ℚ), padic_valued_valuation_p p],
 end

lemma padic'_int.height_one_ideal_def : 
  (padic'_int.height_one_ideal p).as_ideal = ideal.span {(p : Z_p p)} := 
discrete_valuation.is_uniformizer_is_generator _ (padic'.valuation_p p)

--TODO: Golf proof!
lemma padic_int_ring_equiv_range :
  (Z_p p).map (padic_equiv p).to_ring_hom = padic_int.subring p :=
begin
  have : (comap_Zp p).to_subring = (padic_int.valuation_subring p).to_subring,
  rw ← valuation_subrings_eq,
  convert this,
  ext x,
  -- rw comap_Zp,
  -- rw ← subring.mem_carrier,
  -- rw ← subring.mem_carrier,
  simp only [subring.mem_carrier, subring.mem_map, --valuation_subring.mem_to_subring, 
  mem_valuation_subring_iff, 
  exists_prop, valuation_subring.mem_comap],
  split,
  { rintros ⟨y, ⟨hy, H⟩⟩,
    rw ← H,
    simp only [valuation_subring.mem_to_subring, valuation_subring.mem_comap,
      ring_equiv.symm_to_ring_hom_apply_to_ring_hom_apply,
    mem_valuation_subring_iff] at hy ⊢,
    exact hy, },
  { intro hx,
    simp at hx,
    use (padic_equiv p).symm.to_ring_hom x,
    split,
    { simp only [valuation_subring.mem_to_subring, mem_valuation_subring_iff],
      exact hx },
    simp only [ring_equiv.to_ring_hom_apply_symm_to_ring_hom_apply],  },
end

noncomputable!
definition padic_int_ring_equiv :  (Z_p p) ≃+* ℤ_[p] :=
(ring_equiv.subring_map _).trans (ring_equiv.subring_congr (padic_int_ring_equiv_range p))



end padic_comparison