/-
Copyright (c) 2023 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import ring_theory.dedekind_domain.adic_valuation
import discrete_valuation_ring.basic
import for_mathlib.laurent_series_iso.old_power_series_adic_completion--only to have fae_int_valuation_apply

open_locale discrete_valuation
open multiplicative

/-!
In this file we prove that starting with a global field and a place, the extension of
the valuation to the completion agrees with the adic valuation on the local field induced by the 
maximal ideal.


** Main result:
* `is_discrete` is the instance of the fact that the extension of the adic valuation to the
  completion is discrete (i.e. surjective onto `ℤₘ₀`)
* `adic_valuation_equals_completion` is the claim that the valuations coincide
-/


/- TODO list:
-- move is_localization.at_prime.discrete_valuation_ring_of_dedekind_domain
  (currently in discrete_valuation_ring.basic, or at least there after my PR) to
  discrete_valuation_ring.global_to_local
-- Replace Kevin's valuation with the adic valuation on any DVR (in mathlib for Dedekind domains)
-- Prove that Kevin's uniformiser coincides with ours
-- Put a valued instance on the field of fractions of a DVR (in mathlib for Dedekind domains)
-- Since the fraction field of the unit ball of a valued field is not definitionally equal to
  the field we don't have a diamond
-- We do not put a `valued`  instance on a finite extension `L` of a valued `K` to avoid the diamond 
  when `L=K`.
-- For the "same" reason we do not put an instance of an `K₀` algebra on the unit ball `L₀` wrt a
  finite extension `L/K`.

-- Upshot: we put valued instances on fields, but not on other rings (there we only
  define the valuation)
-- When working with the basics about field extensions we only put valuations rather than valued
  instances in order to be able to adapt it to the setting of a finite ext. of number fields with
    some chosen valuation.
-/

noncomputable theory

open is_dedekind_domain is_dedekind_domain.height_one_spectrum valuation

namespace is_dedekind_domain.height_one_spectrum.completion

variables (R : Type*) [comm_ring R] [is_domain R] [is_dedekind_domain R] (v : height_one_spectrum R)
variables (K : Type*) [field K] [algebra R K] [is_fraction_ring R K]
  

local notation `R_v` := adic_completion_integers K v 
local notation `K_v` := adic_completion K v

instance is_discrete : 
  is_discrete (@valued.v K_v _ ℤₘ₀ _ _) := 
begin
  obtain ⟨π, hπ⟩ := valuation_exists_uniformizer K v,
  apply is_discrete_of_exists_uniformizer,
  swap,
  use (↑π : K_v),
  rw [is_uniformizer_iff, ← hπ],
  convert @valued.extension_extends K _ _ _ (valued.mk' v.valuation) π,
end

def max_ideal_of_completion_def : ideal R_v :=
local_ring.maximal_ideal R_v 

instance : discrete_valuation_ring R_v := discrete_valuation.dvr_of_is_discrete _

/- When viewing `K_v` as the completion of `K`, its `valued` instance comes from the completion of 
the valuation on `K`, and this is of course different from the `valued` instance on the fraction
field of `R_v`, itself isomorphic to `K_v`, that instead comes from the `discrete_valuation_ring`
instance on `R_v`. -/
example : valued K_v ℤₘ₀ := height_one_spectrum.valued_adic_completion K v
example : valued (fraction_ring R_v) ℤₘ₀ := discrete_valuation.with_zero.valued

-- TODO: clean up
lemma is_dedekind_domain.height_one_spectrum.valuation_completion_integers_exists_uniformizer : 
  ∃ (π : R_v), valued.v (π : K_v) = of_add (-1 : ℤ) :=
begin 
  obtain ⟨x, hx⟩ := is_dedekind_domain.height_one_spectrum.int_valuation_exists_uniformizer v,
  have h : algebra_map R_v K_v (↑x) = (↑((↑x) : K) : K_v) := rfl,
  use ⟨algebra_map R_v K_v (↑x),
    by simp only [valuation_subring.algebra_map_apply, set_like.coe_mem]⟩,
  simp_rw h,
  --simp only [valuation_subring.algebra_map_apply, set_like.eta],
  rw ← hx, 
  simp only [set_like.coe_mk],/- , valued.valued_completion_apply] -/
  rw is_dedekind_domain.height_one_spectrum.valued_adic_completion_def,
  rw valued.extension_extends,
  have h1 : (↑x : K) = algebra_map R K x := rfl,
  rw h1,
  have h2 : v.int_valuation_def x = v.int_valuation x := rfl,
  rw h2,
  rw ← @is_dedekind_domain.height_one_spectrum.valuation_of_algebra_map R _ _ _ K _ _ _ v x,
  refl,
end

lemma is_dedekind_domain.height_one_spectrum.valuation_completion_exists_uniformizer : 
  ∃ (π : K_v), valued.v π = of_add (-1 : ℤ) :=
begin
  obtain ⟨x, hx⟩ := is_dedekind_domain.height_one_spectrum.valuation_exists_uniformizer K v,
  use ↑x,
  rw [is_dedekind_domain.height_one_spectrum.valued_adic_completion_def, ← hx,
    valued.extension_extends],
  refl,
end

lemma adic_completion_integers_not_is_field :
  ¬ is_field ↥(height_one_spectrum.adic_completion_integers K v) :=
begin
  rw ring.not_is_field_iff_exists_ideal_bot_lt_and_lt_top,
  use max_ideal_of_completion_def R v K,
  split,
  { rw [bot_lt_iff_ne_bot, ne.def],
    by_contra h,
    obtain ⟨π, hπ⟩ :=
    is_dedekind_domain.height_one_spectrum.valuation_completion_integers_exists_uniformizer R v K,
    have h1 : π ∈ max_ideal_of_completion_def R v K,
    { rw [max_ideal_of_completion_def, local_ring.mem_maximal_ideal, mem_nonunits_iff,
        valuation.integer.not_is_unit_iff_valuation_lt_one, hπ],
      exact with_zero.of_add_neg_one_lt_one },
    rw [h, ideal.mem_bot] at h1,
    simp only [h1, algebra_map.coe_zero, valuation.map_zero, with_zero.zero_ne_coe] at hπ,
    exact hπ },
  { simp only [lt_top_iff_ne_top, ne.def, ideal.eq_top_iff_one, max_ideal_of_completion_def,
      local_ring.mem_maximal_ideal, one_not_mem_nonunits, not_false_iff] }
end


def max_ideal_of_completion : height_one_spectrum R_v :=
{ as_ideal := max_ideal_of_completion_def R v K,
  is_prime := ideal.is_maximal.is_prime (local_ring.maximal_ideal.is_maximal R_v),
  ne_bot   := begin
    rw [ne.def, max_ideal_of_completion_def, ← local_ring.is_field_iff_maximal_ideal_eq],
    exact adic_completion_integers_not_is_field R v K,
  end }

--#where

-- def adic_int_valuation : _root_.valuation R_v ℤₘ₀ :=
-- (max_ideal_of_completion R v K).int_valuation

-- def adic_valuation : _root_.valuation K_v ℤₘ₀ :=
-- (max_ideal_of_completion R v K).valuation

local notation `v_adic_of_compl` :=-- valuation K_v ℤₘ₀ := 
  (@is_dedekind_domain.height_one_spectrum.valuation R_v _ _ _ K_v _ _ _ (max_ideal_of_completion R v K))

local notation `v_compl_of_adic` := (valued.v : valuation K_v ℤₘ₀)

open local_ring discretely_valued--needed!

-- open_locale classical --needed?


lemma uno' (L : Type*) [field L] {w : valuation L ℤₘ₀} [is_discrete w]
  [discrete_valuation_ring w.valuation_subring] --shouldn't this follow from is_discrete?
  (x : w.valuation_subring) (n : ℕ) :  w x ≤ of_add (-(n : ℤ)) ↔
    (local_ring.maximal_ideal (w.valuation_subring)) ^ n ∣ ideal.span {x} :=
begin
  by_cases hx : x = 0,
  { simp_rw [ideal.span_singleton_eq_bot.mpr hx, hx, algebra_map.coe_zero,
    valuation.map_zero, with_zero.zero_le, true_iff, ← ideal.zero_eq_bot, dvd_zero] },
  { set r := submodule.is_principal.generator (local_ring.maximal_ideal (w.valuation_subring))
      with hr,
    
    -- have hr₁ : w r = of_add (-(1 : ℤ)), sorry,
    have hrn : w (r ^ n) = of_add (-(n : ℤ)),
    { have := submodule.is_principal.span_singleton_generator (maximal_ideal (w.valuation_subring)),
      rw ← hr at this,
      replace this := discrete_valuation.is_uniformizer_of_generator w this.symm,
      rw is_uniformizer_iff at this,
      simp only [this, valuation.map_pow, of_add_neg, with_zero.coe_inv, inv_pow, inv_inj, 
        ← with_zero.coe_pow, ← of_add_nsmul, nat.smul_one_eq_coe],  },
    have := @valuation.integers.le_iff_dvd L ℤₘ₀ _ _ w w.valuation_subring _ _ (
       valuation.integer.integers w) x (r ^ n),
    rw ← hrn,
    erw this,
    rw ← ideal.span_singleton_generator (local_ring.maximal_ideal (w.valuation_subring)),
    rw ← hr,
    rw ideal.span_singleton_pow,
    rw ideal.dvd_iff_le,
    rw ideal.span_singleton_le_iff_mem,
    rw ideal.mem_span_singleton',
    rwa dvd_iff_exists_eq_mul_left,
    tauto },
end


lemma due (L : Type*) [field L] {w : valuation L ℤₘ₀} (a : w.valuation_subring)
  (b : non_zero_divisors w.valuation_subring) : 
  w (is_localization.mk' L a b) = w a / w b :=  
begin
  rw [div_eq_mul_inv, ← map_inv₀, ← valuation.map_mul],
  apply congr_arg,
  simp only [is_fraction_ring.mk'_eq_div, valuation_subring.algebra_map_apply, _root_.coe_coe, 
    div_eq_mul_inv],
end

lemma aux_for_below (a : R_v) : ((max_ideal_of_completion R v K).int_valuation) 
  a = valued.v (a : K_v) :=
begin
  by_cases ha : a = 0,
  { simp only [ha, valuation.map_zero, algebra_map.coe_zero] },
  { rw fae_int_valuation_apply,
    apply le_antisymm,
    { obtain ⟨n, hn⟩ : ∃ n : ℕ, v_compl_of_adic a = of_add (-n : ℤ), 
      { replace ha : v_compl_of_adic a ≠ 0 := by rwa [valuation.ne_zero_iff, ne.def, subring.coe_eq_zero_iff],
        have := (mem_integer v_compl_of_adic ↑a).mp a.2,
        obtain ⟨α, hα⟩ := with_zero.ne_zero_iff_exists.mp ha,
        rw ← hα at this,
        rw ← with_zero.coe_one at this,
        rw ← of_add_zero at this,
        rw with_zero.coe_le_coe at this,
        rw [← of_add_to_add α] at this,        
        rw multiplicative.of_add_le at this,
        obtain ⟨n, hn⟩ := int.exists_eq_neg_of_nat this,
        use n,
        rw ← hα,
        rw with_zero.coe_inj,
        rw [← of_add_to_add α],
        rw hn },
      -- dsimp only [v_compl_of_adic] at hn,
      rw hn,
      rw int_valuation_le_pow_iff_dvd,
      apply (uno' K_v _ n).mp (le_of_eq hn), },
    { obtain ⟨m, hm⟩ : ∃ m : ℕ, v_adic_of_compl a = of_add (-m : ℤ),
      { replace ha : v_adic_of_compl a ≠ 0 := by rwa [valuation.ne_zero_iff, ne.def,
        subring.coe_eq_zero_iff],
          -- dsimp only [v_adic_of_compl] at ha ⊢,
          have : (max_ideal_of_completion R v K).valuation (↑a : K_v) ≤ 1 := valuation_le_one _ _,
          obtain ⟨α, hα⟩ := with_zero.ne_zero_iff_exists.mp ha,
          rw ← hα at this,
          rw ← with_zero.coe_one at this,
          rw ← of_add_zero at this,
          rw with_zero.coe_le_coe at this,
          rw [← of_add_to_add α] at this,        
          rw multiplicative.of_add_le at this,
          obtain ⟨m, hm⟩ := int.exists_eq_neg_of_nat this,
          use m,
          rw ← hα,
          rw with_zero.coe_inj,
          rw [← of_add_to_add α],
          rw hm, },
      erw valuation_of_algebra_map at hm,
      rw fae_int_valuation_apply at hm,
      rw hm,
      replace hm := le_of_eq hm,
      rw int_valuation_le_pow_iff_dvd at hm,
      rw uno' K_v _ m,
      apply hm,
      apply_instance,
      apply_instance, }},
end

lemma valuation.adic_of_compl_eq_compl_of_adic (x : K_v) : v_adic_of_compl x = v_compl_of_adic x :=
begin
  obtain ⟨a, b, H⟩ := is_localization.mk'_surjective (non_zero_divisors R_v) x, 
  have h2 := due K_v a b,
  have h1 := @valuation_of_mk' R_v _ _ _ K_v _ _ _ (max_ideal_of_completion R v K) a b,
  rw H at h1 h2,
  rw [h1, h2],
  congr;
  apply aux_for_below,
end

end is_dedekind_domain.height_one_spectrum.completion