import ring_theory.dedekind_domain.adic_valuation
import discrete_valuation_ring.basic

open_locale discrete_valuation
open multiplicative

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

-- end unramified

--#check e(K, L)

-- #lint

-- #check ideal.ramification_idx (algebra_map : K₀ →+* (hw.v.integer))
--   (local_ring.maximal_ideal K₀) (local_ring.maximal_ideal hw.v.integer)

noncomputable theory

open is_dedekind_domain is_dedekind_domain.height_one_spectrum valuation

namespace is_dedekind_domain.height_one_spectrum.completion

variables (R : Type*) [comm_ring R] [is_domain R] [is_dedekind_domain R]
  (K : Type*) [field K] [algebra R K] [is_fraction_ring R K]
  (v : height_one_spectrum R)

local notation `R_v` := adic_completion_integers K v 
local notation `K_v` := adic_completion K v

noncomputable! instance : is_discrete (@valued.v K_v _ ℤₘ₀ _ _) := 
begin
  obtain ⟨π, hπ⟩ := valuation_exists_uniformizer K v,
  apply is_discrete_of_exists_uniformizer,
  swap,
  use (↑π : K_v),
  rw [is_uniformizer_iff, ← hπ],
  convert @valued.extension_extends K _ _ _ (valued.mk' v.valuation) π,
end


lemma valued.add_eq_max_of_ne {S Γ₀ : Type*} [comm_ring S]
  [linear_ordered_comm_group_with_zero Γ₀] [valued S Γ₀] {a b : S} (hne : valued.v a ≠ valued.v b) :
  valued.v (a + b) = max (valued.v a) (valued.v b) :=
begin
  wlog hle : valued.v b ≤ valued.v a generalizing b a with H,
  { rw [add_comm, max_comm],
    exact H hne.symm (le_of_lt (not_le.mp hle)), },
  { have hlt : valued.v b  < valued.v a, from lt_of_le_of_ne hle hne.symm,
    have : valued.v a  ≤ max (valued.v (a + b)) (valued.v b), from calc
      valued.v a = valued.v (a + b + (-b)) : by rw [add_neg_cancel_right]
                ... ≤ max (valued.v (a + b)) (valued.v (-b)) : valuation.map_add _ _ _
                ... = max (valued.v (a + b)) (valued.v b ) : by rw valuation.map_neg _ _,
    have hnge : valued.v b  ≤ valued.v (a + b),
    { apply le_of_not_gt,
      intro hgt,
      rw max_eq_right_of_lt hgt at this,
      apply not_lt_of_ge this,
      assumption },
    have : valued.v a ≤ valued.v (a + b), by rwa [max_eq_left hnge] at this,
    apply le_antisymm,
    { exact valuation.map_add _ _ _, },
    { rw max_eq_left_of_lt hlt,
      assumption }},
end


--already done above?
lemma valuation_eq_one_of_is_unit {a : ↥(height_one_spectrum.adic_completion_integers K v)}
  (ha : is_unit a) : valued.v (a : K_v) = (1 : ℤₘ₀) :=
begin
  rw is_unit_iff_exists_inv at ha,
  obtain ⟨b, hab⟩ := ha,
  have hab' : valued.v (a * b : K_v) = (1 : ℤₘ₀),
  { rw [← subring.coe_mul, hab, subring.coe_one, valuation.map_one] },
  rw valuation.map_mul at hab',
  exact eq_one_of_one_le_mul_left a.2 b.2 (le_of_eq hab'.symm),
end


noncomputable! def max_ideal_of_completion_def : ideal R_v :=
local_ring.maximal_ideal R_v 

instance : discrete_valuation_ring R_v :=
disc_valued.discrete_valuation_ring K_v


--TODO: clean up
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
  rw [is_dedekind_domain.height_one_spectrum.valued_adic_completion_def, ← hx, valued.extension_extends],
  refl,
end

lemma adic_completion_integers_not_is_field :
  ¬ is_field ↥(height_one_spectrum.adic_completion_integers K v) :=
begin
  rw ring.not_is_field_iff_exists_ideal_bot_lt_and_lt_top,
  use max_ideal_of_completion_def R K v,
  split,
  { rw [bot_lt_iff_ne_bot, ne.def],
    by_contra h,
    obtain ⟨π, hπ⟩ :=
    is_dedekind_domain.height_one_spectrum.valuation_completion_integers_exists_uniformizer R K v,
    have h1 : π ∈ max_ideal_of_completion_def R K v,
    { rw [max_ideal_of_completion_def, local_ring.mem_maximal_ideal, mem_nonunits_iff,
        valuation.integer.not_is_unit_iff_valuation_lt_one, hπ],
      exact with_zero.of_add_neg_one_lt_one },
    rw [h, ideal.mem_bot] at h1,
    simp only [h1, algebra_map.coe_zero, valuation.map_zero, with_zero.zero_ne_coe] at hπ,
    exact hπ },
  { simp only [lt_top_iff_ne_top, ne.def, ideal.eq_top_iff_one, max_ideal_of_completion_def,
      local_ring.mem_maximal_ideal, one_not_mem_nonunits, not_false_iff] }
end


noncomputable! def max_ideal_of_completion : height_one_spectrum R_v :=
{ as_ideal := max_ideal_of_completion_def R K v,
  is_prime := ideal.is_maximal.is_prime (local_ring.maximal_ideal.is_maximal R_v),
  ne_bot   := begin
    rw [ne.def, max_ideal_of_completion_def, ← local_ring.is_field_iff_maximal_ideal_eq],
    exact adic_completion_integers_not_is_field R K v,
  end }

#where

noncomputable def adic_int_valuation : _root_.valuation R_v ℤₘ₀ :=
(max_ideal_of_completion R K v).int_valuation

noncomputable def adic_valuation : _root_.valuation K_v ℤₘ₀ :=
(max_ideal_of_completion R K v).valuation

/- example : has_zero ℤₘ₀ := with_zero.has_zero

lemma test : false :=
begin
  let a := (@with_zero.has_zero (multiplicative ℤ)).zero,
  let b := (@mul_zero_class.to_has_zero ℤₘ₀ _).zero,
  have : a = b,
  refl,
end -/

open_locale with_zero_topology

/-We are probably trying to prove that starting with a global field and a place, the extension of
the valuation to the completion agrees with the DVR valuation on the local field induced by the 
maximal ideal.
-/

lemma a (x : K_v) : true :=
begin
--letI top : topological_space ℤₘ₀ := with_zero_topology.topological_space,
--letI : valued K ℤₘ₀ := valued.mk' v.valuation,
--have h1 := @valued.continuous_valuation K_v _ ℤₘ₀ _ _,
--have h2 := @valued.continuous_extension K _ ℤₘ₀ _ _,
have h3 : continuous (adic_valuation R K v),
{ --exact valued.continuous_valuation,
  rw continuous_iff_continuous_at,
  intros x,
  rcases eq_or_ne x 0 with rfl|h,
  { rw [continuous_at, valuation.map_zero, with_zero_topology.tendsto_zero],
    intros γ hγ,
    rw [filter.eventually, valued.mem_nhds_zero],
    refine ⟨units.mk0 γ hγ, _⟩,
    intros z hz,
    simp only [set.mem_set_of_eq, units.coe_mk0] at hz ⊢,
    sorry,
     },
  sorry,
  /- { have h := @with_zero_topology.tendsto_zero K_v ℤₘ₀ _ (nhds 0)(val R K v),
    rw [continuous_at, map_zero],
    rw h,
    intros γ hγ,
    rw [filter.eventually, valued.mem_nhds_zero],
    use [units.mk0 γ hγ, subset.rfl] }, -/
  /- rcases eq_or_ne x 0 with rfl|h,
  { rw [continuous_at, map_zero, with_zero_topology.tendsto_zero],
    intros γ hγ,
    rw [filter.eventually, valued.mem_nhds_zero],
    use [units.mk0 γ hγ, subset.rfl] },
  { have v_ne : (v x : Γ₀) ≠ 0, from (valuation.ne_zero_iff _).mpr h,
    rw [continuous_at, with_zero_topology.tendsto_of_ne_zero v_ne],
    apply valued.loc_const v_ne },-/ },
  triv,
--continuous (@valued.v K_v _ ℤₘ₀ _ _)
end

lemma valuations_eq_on_K  (x : K) : (adic_valuation R K v) ↑x = (valued.mk' v.valuation).v x :=
begin
  rw adic_valuation,
  sorry
end

lemma continuous_adic_valuation : continuous (adic_valuation R K v) :=
begin
  sorry
end

lemma valuations_eq (x : K_v) : adic_valuation R K v x = valued.v x :=
begin
  have heq : (adic_valuation R K v).to_fun = valued.v,
  { letI : valued K ℤₘ₀ := valued.mk' v.valuation,
    apply uniform_space.completion.ext (continuous_adic_valuation R K v) valued.continuous_extension,
    intros x,
    rw valued.extension_extends,
    exact valuations_eq_on_K R K v x, },
  rw ← heq,
  refl,
end

section fae

open is_dedekind_domain.height_one_spectrum.

example : is_principal_ideal_ring R_v :=
begin
  exact discrete_valuation_ring.to_is_principal_ideal_ring,
end

lemma exists_double_uniformizer : ∃ π₁ π₂: R_v, 
  valued.v (↑π₁ : K_v) = of_add (-1 : ℤ) ∧ adic_valuation R K v π₂ = of_add (-1 : ℤ) :=
begin
  obtain ⟨π₁, h1⟩ := valuation_completion_exists_uniformizer R K v,
  haveI := (is_principal_ideal_ring_iff R_v).mp discrete_valuation_ring.to_is_principal_ideal_ring
    (max_ideal_of_completion R K v).1,
  let π₂ := ↑(submodule.is_principal.generator (max_ideal_of_completion R K v).1),
  have h2 : adic_valuation R K v π₂ = of_add (-1 : ℤ), sorry,
  sorry,
  -- use [π₁, π₂],
  -- ⟨h1, h2⟩],
end

lemma integral_is_integral (α : R_v) :
  valued.v (↑α : K_v) ≤ of_add (0 : ℤ) ∧ adic_valuation R K v α ≤ of_add (0 : ℤ) :=
begin
  split,
  { let w : valuation K_v ℤₘ₀ := valued.v,
    have := α.2,
    rw ← valuation_subring.valuation_le_one_iff at this,
    convert this,
    sorry,
    },
  { apply @valuation_le_one R_v _ _ _ K_v _ _ _ (max_ideal_of_completion R K v) α }
end

-- #check exists_double_uniformizer R K v
include R K v
lemma foo : true :=
begin
  obtain ⟨ϖ₁, h1⟩ := valuation_completion_integers_exists_uniformizer R K v,
  set v₁ : valuation K_v ℤₘ₀ := valued.v with hv1,
  set v₂ : valuation K_v ℤₘ₀ := adic_valuation R K v with hv2,
  let π₁ : uniformizer v₁ := uniformizer.mk' v₁ ϖ₁ ((is_uniformizer_iff).mp h1),

  haveI := (is_principal_ideal_ring_iff R_v).mp discrete_valuation_ring.to_is_principal_ideal_ring
    (max_ideal_of_completion R K v).1,
  let ϖ₂ := submodule.is_principal.generator (max_ideal_of_completion R K v).1,
  have h_nz_2 : ϖ₂ ≠ 0, sorry,
  have h2 : adic_valuation R K v ϖ₂ = of_add (-1 : ℤ), sorry,
  let π₂ : uniformizer v₂ := uniformizer.mk' v₂ ϖ₂ ((is_uniformizer_iff).mp h2),

  -- let d := v₁ (↑ϖ₂ : K_v),
  -- -- have : d ≤ of_add (0 : ℤ) := (integral_is_integral R K v π₂).1,
  -- -- have := uniformizer_ne_zero v₂ π₂.2,
  obtain ⟨n, ⟨u, hu⟩⟩ := pow_uniformizer v₁ π₁ h_nz_2,
  have key : v₂ (π₁.val) = of_add (-1 : ℤ),
  { apply_fun (v₂ ∘ coe) at hu,
    simp only [function.comp_app, subring.coe_mul, subring.coe_pow, valuation.map_mul,
      valuation.map_pow] at hu,
    rw h2 at hu,
    have := valuation_eq_one_of_is_unit R K v _,
    -- simp only [of_add_neg, with_zero.coe_inv] at hu,

  },
end

end fae

end is_dedekind_domain.height_one_spectrum.completion