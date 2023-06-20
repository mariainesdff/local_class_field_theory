/-
Copyright (c) 2023 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import discrete_valuation_ring.basic
import number_theory.padics.padic_integers
import ring_theory.dedekind_domain.adic_valuation


noncomputable theory

open is_dedekind_domain is_dedekind_domain.height_one_spectrum nnreal polynomial valuation
open_locale nnreal discrete_valuation

def int.p_height_one_ideal (p : out_param ℕ) [hp : fact (p.prime)] : 
  height_one_spectrum ℤ :=
{ as_ideal := ideal.span{(p : ℤ)},
  is_prime := by { rw ideal.span_singleton_prime, 
    exacts [nat.prime_iff_prime_int.mp hp.1, nat.cast_ne_zero.mpr hp.1.ne_zero] },
  ne_bot   := by {simp only [ne.def, ideal.span_singleton_eq_bot, nat.cast_eq_zero],
    exact hp.1.ne_zero, }}
open int

section padic

open padic

variables (p : out_param ℕ) [fact (p.prime)]
  
include p

local attribute [-instance] rat.metric_space rat.normed_field rat.densely_normed_field
  /- rat.normed_linear_ordered_field -/  rat.division_ring rat.normed_add_comm_group

instance : separated_space ℚ_[p] := metric_space.to_separated

def padic_valued : valued ℚ ℤₘ₀ := (p_height_one_ideal p).adic_valued

local attribute [instance] padic_valued

lemma padic_norm_eq_val_norm (x : ℚ) : ((padic_norm p x) : ℝ)  =
  with_zero_mult_int_to_nnreal (ne_zero.ne p) (valued.v x) := sorry

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

instance : is_discrete (@valued.v (Q_p p) _ ℤₘ₀ _ _) := sorry

-- instance : field (Q_p p) := adic_completion.field ℚ (p_height_one_ideal p)

-- instance : valued (Q_p p) ℤₘ₀ := (p_height_one_ideal p).valued_adic_completion ℚ

-- instance : complete_space (Q_p p) := (p_height_one_ideal p).adic_completion_complete_space ℚ

-- instance : has_coe_t ℚ (Q_p p) := uniform_space.completion.has_coe_t ℚ

-- def of_Q : ℚ → (Q_p p) := (@rat.cast_coe _ _).1

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


noncomputable!
definition padic_ring_equiv : (Q_p p) ≃+* ℚ_[p] :=
{ map_mul' := by {rw ← extension_eq_compare p, use (extension_as_ring_hom p).map_mul'},
  map_add' := by {rw ← extension_eq_compare p, exact (extension_as_ring_hom p).map_add'},
  ..(compare p) 
  }

instance : char_zero (Q_p p) := (padic_ring_equiv p).to_ring_hom.char_zero

-- local notation `Z_p` p := (@valued.v (Q_p p) _ ℤₘ₀ _ _).valuation_subring
@[reducible]
def Z_p := (@valued.v (Q_p p) _ ℤₘ₀ _ _).valuation_subring


/- The lemma `padic_int_ring_equiv_mem` states that an element `x ∈ ℚ_[p]` is in `ℤ_[p]` if and
only if it is in the image of `Z_p p` via the ring equivalence `padic_ring_equiv p`. See
`padic_int_ring_equiv` for an upgrade of this statement to a ring equivalence `Z_p p ≃+* ℤ_[p]`-/

set_option profiler true

def padic_int.valuation_subring : valuation_subring ℚ_[p] :=
{ to_subring := padic_int.subring p,
  mem_or_inv_mem' :=
begin
  have not_field : ¬is_field ℤ_[p] := (discrete_valuation_ring.not_is_field _),
  have := ((discrete_valuation_ring.tfae ℤ_[p] not_field).out 0 1).mp
    padic_int.discrete_valuation_ring,
  have cc := (valuation_ring.iff_is_integer_or_is_integer ℤ_[p] ℚ_[p]).mp this,
  intros x,
  specialize cc x,
  cases cc with hx hx,
  { apply or.intro_left,
    obtain ⟨y, hy⟩ := hx,
    rw ← hy,
    simp only [padic_int.algebra_map_apply, subring.mem_carrier, padic_int.mem_subring_iff,
      padic_int.padic_norm_e_of_padic_int],
    apply padic_int.norm_le_one,
    },
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

def another_subring : valuation_subring ℚ_[p] :=
valuation_subring.comap (Z_p p) (padic_ring_equiv p).symm.to_ring_hom

lemma padic_int.nonunit_mem_iff_top_nilpotent (x : ℚ_[p]) :
  x ∈ (padic_int.valuation_subring p).nonunits ↔ filter.tendsto (λ n : ℕ, x ^ n) at_top (𝓝 0) :=
sorry

lemma unit_ball.nonunit_mem_iff_top_nilpotent (x : (Q_p p)) :
  x ∈ (Z_p p).nonunits ↔ filter.tendsto (λ n : ℕ, x ^ n) at_top (𝓝 0) :=
sorry

lemma mem_nonunits_iff_comap (x : (Q_p p)) :
  x ∈ (Z_p p).nonunits ↔ (padic_ring_equiv p) x ∈ (another_subring p).nonunits :=
sorry

lemma key : padic_int.valuation_subring p = another_subring p :=
begin
  rw ← valuation_subring.nonunits_inj,
  ext x,
  split,
  { intro hx,
    rw padic_int.nonunit_mem_iff_top_nilpotent at hx,
    sorry,},
  { intro hx,
    sorry,  },
end


--TODO: Golf proof!
lemma padic_int_ring_equiv_range :
  (Z_p p).map (padic_ring_equiv p).to_ring_hom = padic_int.subring p :=
begin
  have : (another_subring p).to_subring = (padic_int.valuation_subring p).to_subring,
  rw ← key,
  convert this,
  ext x,
  rw another_subring,
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
    use (padic_ring_equiv p).symm.to_ring_hom x,
    split,
    { simp only [valuation_subring.mem_to_subring, mem_valuation_subring_iff],
      exact hx },
    simp only [ring_equiv.to_ring_hom_apply_symm_to_ring_hom_apply],  },
end

-- lemma padic_int_ring_equiv_mem (x : ℚ_[p]) :
--   x ∈ ((Z_p p).map (padic_ring_equiv p).to_ring_hom) ↔ x ∈ padic_int.subring p :=
-- begin
--   split,
--   { intro h,
--     rw padic_int.mem_subring_iff,
--     obtain ⟨z, hz_val, hzx⟩ := h,
--     rw ← hzx,
--     sorry
--   },
--   { intro h,
--     rw padic_int.mem_subring_iff at h,
--     sorry,  
--   },
-- end

-- lemma padic_int_ring_equiv_range' :
--   (Z_p p).map (padic_ring_equiv p).to_ring_hom = padic_int.subring p :=
-- by {ext, rw padic_int_ring_equiv_mem}

noncomputable!
definition padic_int_ring_equiv :  (Z_p p) ≃+* ℤ_[p] :=
(ring_equiv.subring_map _).trans (ring_equiv.subring_congr (padic_int_ring_equiv_range p))




-- instance padic.valued : valued ℚ_[p] ℤₘ₀ :=
-- { v := 
--   { to_fun    := λ x, valued.v ((padic_ring_equiv p).symm x),
--     map_zero' := sorry,
--     map_one'  := sorry,
--     map_mul'  := sorry,
--     map_add_le_max' := sorry },--,
--     is_topological_valuation := sorry,
--   ..(infer_instance : uniform_space ℚ_[p]),
--   ..non_unital_normed_ring.to_normed_add_comm_group }

end padic