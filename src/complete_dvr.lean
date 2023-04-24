import number_theory.ramification_inertia
import ring_theory.dedekind_domain.adic_valuation
import ring_theory.discrete_valuation_ring
import ring_theory.valuation.tfae
import topology.algebra.valued_field
import topology.algebra.with_zero_topology
import from_mathlib.rank_one_valuation

namespace with_zero

open_locale discrete_valuation

lemma of_add_neg_one_le_one : ((multiplicative.of_add ((-1 : ℤ))) : ℤₘ₀) < (1 : ℤₘ₀) := 
begin
  rw [← with_zero.coe_one, with_zero.coe_lt_coe, ← of_add_zero],
  exact neg_one_lt_zero,
end

end with_zero

namespace valuation

open is_dedekind_domain function
open_locale discrete_valuation

variables {A : Type*} [comm_ring A] 

lemma add_eq_max_of_ne {Γ₀ : Type*} [linear_ordered_comm_group_with_zero Γ₀]
  {v : valuation A Γ₀} {a b : A} (hne : v a ≠ v b) : v (a + b) = max (v a) (v b) :=
begin
  wlog hle : v b ≤ v a generalizing b a with H,
  { rw [add_comm, max_comm],
    exact H hne.symm (le_of_lt (not_le.mp hle)), },
  { have hlt : v b  < v a, from lt_of_le_of_ne hle hne.symm,
    have : v a  ≤ max (v (a + b)) (v b), from calc
      v a = v (a + b + (-b)) : by rw [add_neg_cancel_right]
                ... ≤ max (v (a + b)) (v (-b)) : valuation.map_add _ _ _
                ... = max (v (a + b)) (v b ) : by rw valuation.map_neg _ _,
    have hnge : v b  ≤ v (a + b),
    { apply le_of_not_gt,
      intro hgt,
      rw max_eq_right_of_lt hgt at this,
      apply not_lt_of_ge this,
      assumption },
    have : v a ≤ v (a + b), by rwa [max_eq_left hnge] at this,
    apply le_antisymm,
    { exact valuation.map_add _ _ _, },
    { rw max_eq_left_of_lt hlt,
      assumption }},
end

lemma mem_integer {Γ₀ : Type*} [linear_ordered_comm_group_with_zero Γ₀] (v : valuation A Γ₀)
  (a : A) : a ∈ v.integer ↔ v a ≤ 1 := iff.rfl

/- We insist that `v` takes values in ℤₘ₀ in order to define uniformizers as the elements in `K`
whose valuation is exactly `with_zero.multiplicative (- 1) : ℤₘ₀`-/
class is_discrete (v : valuation A ℤₘ₀) :=
(surj : surjective v)

namespace discrete_valuation

open valuation ideal
open_locale discrete_valuation

section basic

variables {K : Type*} [field K] [hv : valued K ℤₘ₀]

local notation `K₀` := hv.v.integer

include hv

definition is_uniformizer (π : hv.v.integer) : Prop := 
  hv.v π = (multiplicative.of_add (- 1 : ℤ) : ℤₘ₀)

variable (K)
@[ext]
structure uniformizer :=
(val : hv.v.integer)
(valuation_eq_neg_one : hv.v val = (multiplicative.of_add (- 1 : ℤ) : ℤₘ₀))

noncomputable
lemma discrete_of_exists_uniformizer (π : uniformizer K) : is_discrete hv.v :=
begin
  fconstructor,
  intro x,
  apply with_zero.cases_on x,
  {use 0,
    simp only [map_zero]},
  { intro m,
    use π.1^(- multiplicative.to_add m),
    simp only [/- zpow_neg, map_inv₀,  -/map_zpow₀],
    rw [π.2, ← with_zero.coe_zpow, with_zero.coe_inj, ← of_add_zsmul, ← zsmul_neg', neg_neg,
      zsmul_one, int.cast_id, of_add_to_add],}
end

variable [is_discrete hv.v]

lemma exists_uniformizer : ∃ π : K₀, is_uniformizer π := 
begin
  letI surj_v : is_discrete hv.v, apply_instance,
  use (surj_v.surj (multiplicative.of_add (- 1 : ℤ) : ℤₘ₀)).some,
  rw mem_integer,
  rw (surj_v.surj (multiplicative.of_add (- 1 : ℤ) : ℤₘ₀)).some_spec,
  exact (le_of_lt with_zero.of_add_neg_one_le_one),
  exact (surj_v.surj (multiplicative.of_add (- 1 : ℤ) : ℤₘ₀)).some_spec,
end

instance : nonempty (uniformizer K) := 
  ⟨⟨(exists_uniformizer K).some, (exists_uniformizer K).some_spec⟩⟩
   
lemma uniformizer_ne_zero {π : K₀} (hπ : is_uniformizer π) : π ≠ 0 := 
begin
  intro h0,
  rw [h0, is_uniformizer, algebra_map.coe_zero, map_zero] at hπ,
  exact with_zero.zero_ne_coe hπ,
end

lemma uniformizer_ne_zero' (π : uniformizer K) : π.1 ≠ 0 := 
begin
  intro h0,
  have := π.2,
  rw [h0, algebra_map.coe_zero, map_zero] at this,
  exact with_zero.zero_ne_coe this,
end

lemma uniformizer_not_is_unit {π : K₀}  (hπ : is_uniformizer π) : ¬ is_unit π := 
begin
  intro h,
  have h1 := @valuation.integers.one_of_is_unit K ℤₘ₀ _ _ hv.v hv.v.integer _ _ 
   (valuation.integer.integers hv.v) π h,
  erw [is_uniformizer, h1] at hπ,
  exact ne_of_gt with_zero.of_add_neg_one_le_one hπ,
end

variables (π : K₀) (hπ : is_uniformizer π)

variable {K}
lemma pow_uniformizer (r : K₀) (hr : r ≠ 0) : ∃ n : ℕ, ∃ u : K₀ˣ, r = π^n * u :=
begin
  have hr₀ : hv.v r ≠ 0, sorry,
  set m := - (with_zero.unzero hr₀).to_add with hm,
  have hm₀ : 0 ≤ m, sorry,
  obtain ⟨n, hn⟩ := int.eq_coe_of_zero_le hm₀,
  use n,
  set x := π.1^(-m) * r with hx,
  have hx₀ : hv.v x = 1, sorry,
  let a : K₀ := ⟨x, by apply le_of_eq hx₀⟩,
  have ha₀ : (↑a : K) ≠ 0, sorry,
  have h_unit_a : is_unit a,
  exact integers.is_unit_of_one (integer.integers hv.v) ((is_unit_iff_ne_zero).mpr ha₀) hx₀,
  use is_unit.unit h_unit_a,
  ext,
  sorry,
end

lemma ideal_is_principal (I : ideal K₀) : I.is_principal:=
begin
  classical,
  obtain ⟨π, hπ⟩ := exists_uniformizer K,
  by_cases hI : I = ⊥,
  {rw hI, exact bot_is_principal},
  { rw ← ne.def at hI,
    obtain ⟨x, ⟨hx_mem, hx₀⟩⟩ := submodule.exists_mem_ne_zero_of_ne_bot hI,
    let P : ℕ → Prop := λ n, π^n ∈ I,
    have H : ∃ n, P n,
    { obtain ⟨n, ⟨u, hu⟩⟩ := pow_uniformizer π x hx₀,
      use n,
      simp_rw P,
      rwa [← mul_unit_mem_iff_mem I u.is_unit, ← hu] },
    let N := nat.find H,
    use π^N,
    ext r,
    split,
    { intro hr,
      by_cases hr₀ : r = 0,
      { rw hr₀, exact zero_mem _ },
      { obtain ⟨m, ⟨u, hu⟩⟩ := pow_uniformizer π r hr₀,
        rw submodule_span_eq,
        rw mem_span_singleton',
        use u * π^(m - N),
        rw [mul_assoc, ← pow_add, nat.sub_add_cancel, mul_comm, hu],
        apply nat.find_min',
        simp_rw P,
        rwa [← mul_unit_mem_iff_mem I u.is_unit, ← hu] } },
    { intro hr,    
      rw submodule_span_eq at hr,
      rw mem_span_singleton' at hr,
      sorry }},
end

lemma not_is_field : ¬ is_field K₀ :=
begin
  obtain ⟨π, hπ⟩ := exists_uniformizer K,
  rintros ⟨-, -, h⟩,
  specialize h (uniformizer_ne_zero K hπ),
  rw ← is_unit_iff_exists_inv at h,
  exact uniformizer_not_is_unit K hπ h,
end

instance is_principal_ideal_ring : is_principal_ideal_ring (hv.v.integer) := 
  ⟨λ I, ideal_is_principal I⟩

-- noncomputable!
instance : local_ring K₀ :=
{ exists_pair_ne := ⟨0, 1, zero_ne_one⟩,
  is_unit_or_is_unit_of_add_one := λ a b hab, 
  begin
    by_cases ha : is_unit a,
    { exact or.inl ha },
    { right,
      have hab' : valued.v (a + b : K) = 
        (1 : ℤₘ₀),
      { rw [← subring.coe_add, hab, subring.coe_one, map_one] },
      have hb : (↑b : K) ≠ 0, sorry,
      apply @integers.is_unit_of_one K _ _ _ hv.v K₀ _ _ (integer.integers hv.v) b
        ((is_unit_iff_ne_zero).mpr hb) _,
      have hab'' : hv.v a < (1 : ℤₘ₀),
      { apply lt_of_le_of_ne,
        apply a.2,
        sorry },
      change hv.v ↑b = 1,
      replace hab'' : hv.v (-a) < hv.v (a + b), sorry,
      rw [← add_sub_cancel' (↑a : K) ↑b],
      rw sub_eq_add_neg,
      rw [add_comm (↑a + ↑b) _],
      rw add_eq_max_of_ne (ne_of_lt hab''),
      sorry },
  end }

-- Chapter I, Section 1, Proposition 1 in Serre's Local Fields
instance discrete_valuation_ring : discrete_valuation_ring (hv.v.integer) := 
  ((discrete_valuation_ring.tfae K₀ not_is_field).out 0 4).mpr $ ideal_is_principal _

end basic

namespace is_dedekind_domain.height_one_spectrum

open is_dedekind_domain is_dedekind_domain.height_one_spectrum

variables (R : Type*) [comm_ring R] [is_domain R] [is_dedekind_domain R]
  (K : Type*) [field K] [algebra R K] [is_fraction_ring R K]
  (v : height_one_spectrum R)

local notation `R_v` := is_dedekind_domain.height_one_spectrum.adic_completion_integers K v 
local notation `K_v` := is_dedekind_domain.height_one_spectrum.adic_completion K v

lemma valuation_completion_exists_uniformizer : 
  ∃ (π : K_v), valued.v π = (multiplicative.of_add ((-1 : ℤ))) :=
begin
  obtain ⟨x, hx⟩ := is_dedekind_domain.height_one_spectrum.valuation_exists_uniformizer K v,
  use ↑x,
  rw [is_dedekind_domain.height_one_spectrum.valued_adic_completion_def, ← hx, 
    valued.extension_extends],
  refl,
end

noncomputable! instance : is_discrete (@valued.v K_v _ ℤₘ₀ _ _) := 
sorry

end is_dedekind_domain.height_one_spectrum


#exit

variables (K : out_param(Type*)) [field K]  [hv : valued K ℤₘ₀] [is_discrete hv.v]
 -- [hu : uniform_space K]

-- Without finite_dimensional, the fails_quickly does not complain
variables (L : Type*) [field L] [algebra K L] [finite_dimensional K L]

include hv

--instance [finite_dimensional K L] : uniform_space L := infer_instance
--instance normed_L : normed_field L := sorry
def hw : valued L ℤₘ₀ := sorry -- May be a bit hard

--is it reasonable to first have the `def` and then this `instance`?
instance : valued L ℤₘ₀ := hw K L

#lint

--instance is_discrete_of_finite : is_discrete (@valued.v L _ ℤₘ₀ _ _) := sorry
instance is_discrete_of_finite : is_discrete (hw K L).v := sorry

/- lemma integral_closure_eq_integer :
  (integral_closure hv.v.integer L).to_subring = (@valued.v L _ ℤₘ₀ _ _).integer :=
sorry -/
lemma integral_closure_eq_integer :
  (integral_closure hv.v.integer L).to_subring = (hw K L).v.integer :=
sorry

--Chapter 2, Section 2, Proposition 3 in Serre's Local Fields
instance : discrete_valuation_ring (integral_closure hv.v.integer L) := sorry

lemma integral_closure_finrank :
  finite_dimensional.finrank hv.v.integer (integral_closure hv.v.integer L) =
  finite_dimensional.finrank K L :=
sorry

/- postfix `₀`:1025:= valued.v.integer

#check K₀ -/

local notation `K₀` := hv.v.integer

local notation `L₀` := (hw K L).v.integer

instance : algebra K₀ L₀ :=
by rw ← integral_closure_eq_integer; exact (integral_closure ↥(valued.v.integer) L).algebra

local notation `e(` K`,`L`)` := ideal.ramification_idx (algebra_map K₀ L₀)
  (local_ring.maximal_ideal K₀) (local_ring.maximal_ideal L₀)

#check e(K, L)

#lint

-- #check ideal.ramification_idx (algebra_map : K₀ →+* (hw.v.integer))
--   (local_ring.maximal_ideal K₀) (local_ring.maximal_ideal hw.v.integer)

end discrete_valuation



noncomputable theory

namespace is_dedekind_domain.height_one_spectrum
variables (R : Type*) [comm_ring R] [is_domain R] [is_dedekind_domain R]
  (K : Type*) [field K] [algebra R K] [is_fraction_ring R K]
  (v : height_one_spectrum R)

local notation `R_v` := is_dedekind_domain.height_one_spectrum.adic_completion_integers K v 
local notation `K_v` := is_dedekind_domain.height_one_spectrum.adic_completion K v

noncomputable! instance : is_discrete (@valued.v K_v _ ℤₘ₀ _ _) := 
sorry

#exit

instance asdf : is_noetherian_ring R_v :=
{ noetherian := sorry }

section

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

end
--already done above?
lemma valuation_eq_one_of_is_unit {a : ↥(height_one_spectrum.adic_completion_integers K v)}
  (ha : is_unit a) : valued.v (a : K_v) = (1 : ℤₘ₀) :=
begin
  rw is_unit_iff_exists_inv at ha,
  obtain ⟨b, hab⟩ := ha,
  have hab' : valued.v (a * b : K_v) = (1 : ℤₘ₀),
  { rw [← subring.coe_mul, hab, subring.coe_one, map_one] },
  rw map_mul at hab',
  exact eq_one_of_one_le_mul_left a.2 b.2 (le_of_eq hab'.symm),
end

--already done above?
lemma is_unit_iff_valuation_eq_one (a : ↥(height_one_spectrum.adic_completion_integers K v)) :
  is_unit a ↔ valued.v (a : K_v) = (1 : ℤₘ₀) :=
begin
  refine ⟨λ ha, valuation_eq_one_of_is_unit R K v ha, λ ha, _⟩,
  have ha0 : (a : K_v) ≠ 0,
  { by_contra h0,
    rw [h0, map_zero] at ha,
    exact zero_ne_one ha, }, 
  have ha' : valued.v (a : K_v)⁻¹ = 
        (1 : ℤₘ₀),
  { rw [map_inv₀, inv_eq_one], exact ha, },
  rw is_unit_iff_exists_inv,
  use (a : K_v)⁻¹,
  { rw mem_adic_completion_integers,
    exact le_of_eq ha' },
  { ext, rw [subring.coe_mul, set_like.coe_mk, algebra_map.coe_one, mul_inv_cancel ha0] },
end

lemma not_is_unit_iff_valuation_lt_one (a : ↥(height_one_spectrum.adic_completion_integers K v)) :
  ¬ is_unit a ↔ valued.v (a : K_v) < (1 : ℤₘ₀) :=
begin
  rw [← not_le, not_iff_not, is_unit_iff_valuation_eq_one, le_antisymm_iff],
  exact and_iff_right a.2,
end

instance : local_ring R_v :=
{ exists_pair_ne := ⟨0, 1, zero_ne_one⟩,
  is_unit_or_is_unit_of_add_one := λ a b hab, 
  begin
    by_cases ha : is_unit a,
    { exact or.inl ha },
    { right,
      have hab' : valued.v (a + b : K_v) = 
        (1 : ℤₘ₀),
      { rw [← subring.coe_add, hab, subring.coe_one, map_one] },
      by_contra hb,
      rw not_is_unit_iff_valuation_lt_one at ha hb,
      have hab'' : valued.v (a + b : K_v) < (1 : ℤₘ₀),
      { apply lt_of_le_of_lt (valuation.map_add _ _ _), -- (max_lt ha hb),
        apply max_lt ha hb, /- diamond on ℤₘ₀ linear order (!) -/},
      exact (ne_of_lt hab'') hab' },

  end }

noncomputable! def completion_max_ideal_def : ideal R_v :=
local_ring.maximal_ideal R_v 

instance /- (hv : ideal.principal ) -/ : discrete_valuation_ring R_v :=
sorry
/- { principal := sorry,
  exists_pair_ne := ⟨0, 1, zero_ne_one⟩,
  is_unit_or_is_unit_of_add_one := sorry,
  not_a_field' := sorry } -/

--TODO: clean up
lemma is_dedekind_domain.height_one_spectrum.valuation_completion_integers_exists_uniformizer : 
  ∃ (π : R_v), valued.v (π : K_v) = (multiplicative.of_add ((-1 : ℤ))) :=
begin 
  obtain ⟨x, hx⟩ := is_dedekind_domain.height_one_spectrum.int_valuation_exists_uniformizer v,
  have h : algebra_map R_v K_v (↑x) = (↑((↑x) : K) : K_v) := rfl,
  use ⟨algebra_map R_v K_v (↑x),
    by simp only [valuation_subring.algebra_map_apply, set_like.coe_mem]⟩,
  simp_rw h,
  --simp only [valuation_subring.algebra_map_apply, set_like.eta],
  rw ← hx, 
  simp only [set_like.coe_mk],/- , valued.valued_completion_apply] -/
  rw valued_adic_completion_def,
  rw valued.extension_extends,
  have h1 : (↑x : K) = algebra_map R K x := rfl,
  rw h1,
  have h2 : v.int_valuation_def x = v.int_valuation x := rfl,
  rw h2,
  rw ← @valuation_of_algebra_map R _ _ _ K _ _ _ v x,
  refl,
end

lemma is_dedekind_domain.height_one_spectrum.valuation_completion_exists_uniformizer : 
  ∃ (π : K_v), valued.v π = (multiplicative.of_add ((-1 : ℤ))) :=
begin
  obtain ⟨x, hx⟩ := is_dedekind_domain.height_one_spectrum.valuation_exists_uniformizer K v,
  use ↑x,
  rw [valued_adic_completion_def, ← hx, valued.extension_extends],
  refl,
end

lemma adic_completion_integers_not_is_field :
  ¬ is_field ↥(height_one_spectrum.adic_completion_integers K v) :=
begin
  rw ring.not_is_field_iff_exists_ideal_bot_lt_and_lt_top,
  use completion_max_ideal_def R K v,
  split,
  { rw [bot_lt_iff_ne_bot, ne.def],
    by_contra h,
    obtain ⟨π, hπ⟩ :=
    is_dedekind_domain.height_one_spectrum.valuation_completion_integers_exists_uniformizer R K v,
    have h1 : π ∈ completion_max_ideal_def R K v,
    { rw [completion_max_ideal_def, local_ring.mem_maximal_ideal, mem_nonunits_iff,
        not_is_unit_iff_valuation_lt_one, hπ],
      exact bar },
    rw [h, ideal.mem_bot] at h1,
    simp only [h1, algebra_map.coe_zero, valuation.map_zero, with_zero.zero_ne_coe] at hπ,
    exact hπ },
  { simp only [lt_top_iff_ne_top, ne.def, ideal.eq_top_iff_one, completion_max_ideal_def,
      local_ring.mem_maximal_ideal, one_not_mem_nonunits, not_false_iff] }
end

noncomputable! def completion_max_ideal : height_one_spectrum R_v :=
{ as_ideal := completion_max_ideal_def R K v,
  is_prime := ideal.is_maximal.is_prime (local_ring.maximal_ideal.is_maximal R_v),
  ne_bot   := begin
    rw [ne.def, completion_max_ideal_def, ← local_ring.is_field_iff_maximal_ideal_eq],
    exact adic_completion_integers_not_is_field R K v,
  end }

noncomputable def val' : _root_.valuation R_v ℤₘ₀ :=
(completion_max_ideal R K v).int_valuation

noncomputable def val : _root_.valuation K_v ℤₘ₀ :=
(completion_max_ideal R K v).valuation


/- example : has_zero ℤₘ₀ := with_zero.has_zero

lemma test : false :=
begin
  let a := (@with_zero.has_zero (multiplicative ℤ)).zero,
  let b := (@mul_zero_class.to_has_zero ℤₘ₀ _).zero,
  have : a = b,
  refl,
end -/

open_locale with_zero_topology


lemma a (x : K_v) : true :=
begin
--letI top : topological_space ℤₘ₀ := with_zero_topology.topological_space,
--letI : valued K ℤₘ₀ := valued.mk' v.valuation,
--have h1 := @valued.continuous_valuation K_v _ ℤₘ₀ _ _,
--have h2 := @valued.continuous_extension K _ ℤₘ₀ _ _,
have h3 : continuous (val R K v),
{ --exact valued.continuous_valuation,
  rw continuous_iff_continuous_at,
  intros x,
  rcases eq_or_ne x 0 with rfl|h,
  { rw [continuous_at, map_zero, with_zero_topology.tendsto_zero],
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

lemma l1 (x : K) : (val R K v) ↑x = ((valued.mk' v.valuation)).v x :=
begin
  rw val,
  sorry
end

lemma l2 : continuous (val R K v).to_monoid_with_zero_hom.to_fun :=
begin
  sorry
end

--set_option pp.implicit true
lemma valuations_eq (x : K_v) : val R K v x = valued.v x :=
begin
  have : (val R K v).to_fun = valued.v,
  { letI : valued K ℤₘ₀ := valued.mk' v.valuation,
    apply uniform_space.completion.ext,
    sorry,
    exact valued.continuous_extension,
    intros x,
    rw valued_adic_completion_def,
    rw valued.extension_extends,
    

    sorry },
  rw ← this,
  refl,
  /- letI : valued K ℤₘ₀ := v.adic_valued,
  apply uniform_space.completion.induction_on x,
  { simp only, --(?)
    sorry },
  intros a,
  sorry -/
end


end is_dedekind_domain.height_one_spectrum

