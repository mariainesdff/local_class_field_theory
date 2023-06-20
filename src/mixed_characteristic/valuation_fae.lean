/-
Copyright (c) 2023 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import from_mathlib.normed_valued
import discrete_valuation_ring.extensions
import number_theory.padics.padic_integers
import ring_theory.dedekind_domain.adic_valuation
import mixed_characteristic.basic


noncomputable theory

open is_dedekind_domain is_dedekind_domain.height_one_spectrum nnreal polynomial valuation
open_locale mixed_char_local_field nnreal discrete_valuation

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

local attribute [-instance] rat.metric_space rat.normed_field 
  rat.normed_linear_ordered_field rat.densely_normed_field rat.division_ring rat.normed_add_comm_group

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
  dense            := dense_coe p,
}

namespace padic'

--`toDO`  do we really need to remove it?
-- local attribute [- instance] rat.cast_coe

def Q_p : Type* := adic_completion ℚ (p_height_one_ideal p)

instance : field (Q_p p) := adic_completion.field ℚ (p_height_one_ideal p)

instance : valued (Q_p p) ℤₘ₀ := (p_height_one_ideal p).valued_adic_completion ℚ

instance : complete_space (Q_p p) := (p_height_one_ideal p).adic_completion_complete_space ℚ

instance : has_coe_t ℚ (Q_p p) := uniform_space.completion.has_coe_t ℚ

def of_Q : ℚ → (Q_p p) := (@rat.cast_coe _ _).1

def padic'_pkg : abstract_completion ℚ :=
{ space            := Q_p p,
  coe              := coe,
  uniform_struct   := infer_instance,
  complete         := infer_instance,
  separation       := infer_instance,
  uniform_inducing := (uniform_space.completion.uniform_embedding_coe ℚ).1,
  dense            := uniform_space.completion.dense_range_coe,
}

end padic'

open padic'

def compare : Q_p p ≃ᵤ ℚ_[p] :=
abstract_completion.compare_equiv (padic'_pkg p) (padic_pkg p)

def coe_ring_hom : ℚ →+* ℚ_[p] :=
{ to_fun    := (padic_pkg p).2,
  map_one'  := rat.cast_one,
  map_mul'  := rat.cast_mul,
  map_zero' := rat.cast_zero,
  map_add'  := rat.cast_add }


/-`[FAE]` The lemmas `coe_is_inducing` and `uniform_continuous_coe` seem to create problems
related to the fact that `metric_space.completion` and `uniform_space.completion` are not defeq.
First close the goals in `padic_pkg`. Also, `extension_as_ring_hom_to_fun` and its siblings might be
redundant
-/

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

local notation `Z_p` p := (@valued.v (Q_p p) _ ℤₘ₀ _ _).valuation_subring

/- The lemma `padic_int_ring_equiv_mem` states that an element `x ∈ ℚ_[p]` is in `ℤ_[p]` if and
only if it is in the image of `Z_p p` via the ring equivalence `padic_ring_equiv p`. See
`padic_int_ring_equiv` for an upgrade of this statement to a ring equivalence `Z_p p ≃+* ℤ_[p]`-/


lemma padic_int_ring_equiv_mem (x : ℚ_[p]) :
  x ∈ ((Z_p p).map (padic_ring_equiv p).to_ring_hom) ↔ x ∈ padic_int.subring p :=
begin
  split,
  { intro h,
    rw padic_int.mem_subring_iff,
    obtain ⟨z, hz_val, hzx⟩ := h,
    rw ← hzx,
    sorry
  },
  { intro h,
    rw padic_int.mem_subring_iff at h,
    sorry,  
  },
end

lemma padic_int_ring_equiv_range :
  (Z_p p).map (padic_ring_equiv p).to_ring_hom = padic_int.subring p :=
by {ext, rw padic_int_ring_equiv_mem}

noncomputable!
definition padic_int_ring_equiv :  (Z_p p) ≃+* ℤ_[p] :=
(ring_equiv.subring_map _).trans (ring_equiv.subring_congr (padic_int_ring_equiv_range p))


instance padic.valued : valued ℚ_[p] ℤₘ₀ :=
{ v := 
  { to_fun    := λ x, valued.v ((padic_ring_equiv p).symm x),
    map_zero' := sorry,
    map_one'  := sorry,
    map_mul'  := sorry,
    map_add_le_max' := sorry },--,
    is_topological_valuation := sorry,
  ..(infer_instance : uniform_space ℚ_[p]),
  ..non_unital_normed_ring.to_normed_add_comm_group }

end padic


#exit

namespace mixed_char_local_field


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
