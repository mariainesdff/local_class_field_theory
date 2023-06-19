/-
Copyright (c) 2023 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import ring_theory.dedekind_domain.adic_valuation
import ring_theory.dedekind_domain.pid
import ring_theory.discrete_valuation_ring
import ring_theory.ideal.basic
import ring_theory.valuation.tfae
import ring_theory.valuation.valuation_subring
import topology.algebra.valued_field
import topology.algebra.with_zero_topology

import for_mathlib.rank_one_valuation
import with_zero

open_locale discrete_valuation nnreal

namespace with_zero

open multiplicative

lemma of_add_neg_nat (n : ℕ) : 
  (of_add (-n : ℤ) : ℤₘ₀) = (of_add (-1 : ℤ))^n :=
by rw [← with_zero.coe_pow, with_zero.coe_inj, ← one_mul (n : ℤ), ← neg_mul, 
  int.of_add_mul, zpow_coe_nat]

lemma of_add_neg_one_lt_one : ((multiplicative.of_add ((-1 : ℤ))) : ℤₘ₀) < (1 : ℤₘ₀) := 
begin
  rw [← with_zero.coe_one, with_zero.coe_lt_coe, ← of_add_zero],
  exact neg_one_lt_zero,
end

end with_zero

namespace valuation

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

lemma add_eq_max_of_lt {Γ₀ : Type*} [linear_ordered_comm_group_with_zero Γ₀]
  {v : valuation A Γ₀} {a b : A} (hlt : v a < v b) : v (a + b) = max (v a) (v b) :=
add_eq_max_of_ne (ne_of_lt (hlt))

lemma mem_integer {Γ₀ : Type*} [linear_ordered_comm_group_with_zero Γ₀] (v : valuation A Γ₀)
  (a : A) : a ∈ v.integer ↔ v a ≤ 1 := iff.rfl

namespace integer

theorem is_unit_iff_valuation_eq_one {K : Type*} [field K] {Γ₀ : Type*} 
  [linear_ordered_comm_group_with_zero Γ₀] {v : valuation K Γ₀} (x : v.integer) : 
  is_unit x ↔ v x = 1 :=
begin
  refine ⟨@integers.one_of_is_unit K Γ₀ _ _ v v.integer _ _ (valuation.integer.integers v) _, 
    λ hx, _⟩,
  have hx0 : (x : K) ≠ 0,
  { by_contra h0,
    rw [h0, map_zero] at hx,
    exact zero_ne_one hx, }, 
  have hx' : v (x : K)⁻¹ = (1 : Γ₀) ,
  { rw [map_inv₀, inv_eq_one], exact hx, },
  rw is_unit_iff_exists_inv,
  use (x : K)⁻¹,
  { rw mem_integer,
    exact le_of_eq hx' },
  { ext, rw [subring.coe_mul, set_like.coe_mk, algebra_map.coe_one, mul_inv_cancel hx0] },
end

lemma not_is_unit_iff_valuation_lt_one {K : Type*} [field K] {Γ₀ : Type*} 
  [linear_ordered_comm_group_with_zero Γ₀] {v : valuation K Γ₀} (x : v.integer) :
  ¬ is_unit x ↔ v x < 1 :=
begin
  rw [← not_le, not_iff_not, is_unit_iff_valuation_eq_one, le_antisymm_iff],
  exact and_iff_right x.2,
end

end integer


/- We insist that `v` takes values in ℤₘ₀ in order to define uniformizers as the elements in `K`
whose valuation is exactly `with_zero.multiplicative (- 1) : ℤₘ₀`-/
class is_discrete (v : valuation A ℤₘ₀) : Prop :=
(surj : function.surjective v)

open valuation ideal is_dedekind_domain multiplicative with_zero

variables {R : Type*} [comm_ring R] (vR : valuation R ℤₘ₀)

def is_uniformizer (π : R) : Prop := 
vR π = (multiplicative.of_add (- 1 : ℤ) : ℤₘ₀)

variable {vR}
lemma is_uniformizer_iff {π : R} : is_uniformizer vR π ↔ 
  vR π = (multiplicative.of_add (- 1 : ℤ) : ℤₘ₀) := refl _

variable (vR)
@[ext] structure uniformizer :=
(val : vR.integer)
(valuation_eq_neg_one : is_uniformizer vR val)

def uniformizer.mk' (x : R) (hx : is_uniformizer vR x) : uniformizer vR :=
{ val := ⟨x, by {rw [mem_integer, is_uniformizer_iff.mp hx],
   exact (le_of_lt with_zero.of_add_neg_one_lt_one)}⟩,
valuation_eq_neg_one := hx }

@[simp]
instance : has_coe (uniformizer vR) vR.integer := ⟨λ π, π.val⟩

@[simp]
lemma uniformizer.val_eq_coe {π : uniformizer vR} : (π : R) = π.val := rfl

lemma is_discrete_of_exists_uniformizer {K : Type*} [field K] (v : valuation K ℤₘ₀) {π : K}
  (hπ : is_uniformizer v π) : is_discrete v :=
begin
  fconstructor,
  intro x,
  apply with_zero.cases_on x,
  { exact ⟨0, valuation.map_zero v⟩ },
  { rw is_uniformizer at hπ,
    intro m,
    use π^(- multiplicative.to_add m),
    rw [map_zpow₀, hπ, ← coe_zpow, coe_inj, ← of_add_zsmul, ← zsmul_neg', neg_neg, zsmul_one,
      int.cast_id, of_add_to_add] }
end

lemma uniformizer_ne_zero {π : R} (hπ : is_uniformizer vR π) : π ≠ 0 := 
begin
  intro h0,
  rw [h0, is_uniformizer, valuation.map_zero] at hπ,
  exact with_zero.zero_ne_coe hπ,
end

lemma uniformizer_ne_zero' (π : uniformizer vR) : π.1.1 ≠ 0 := 
uniformizer_ne_zero vR π.2

lemma uniformizer_valuation_pos {π : R} (hπ : is_uniformizer vR π) : 0 < vR π := 
  by {rw is_uniformizer_iff at hπ, simp only [zero_lt_iff, ne.def, hπ, coe_ne_zero, not_false_iff]}

lemma uniformizer_not_is_unit {π : vR.integer} (hπ : is_uniformizer vR π ) : ¬ is_unit π := 
begin
  intro h,
  have h1 := @valuation.integers.one_of_is_unit R ℤₘ₀ _ _ vR vR.integer _ _ 
   (valuation.integer.integers vR) π h,
  erw [is_uniformizer, h1] at hπ,
  exact ne_of_gt of_add_neg_one_lt_one hπ,
end

lemma uniformizer_valuation_lt_one {π : R} (hπ : is_uniformizer vR π) : vR π < 1 := 
by {rw is_uniformizer_iff.mp hπ, exact of_add_neg_one_lt_one}

open_locale nnreal

/-- If the residue field is finite, then `valuation_base` is the cardinal of the residue field, and
otherwise it takes the value `6` which is not a prime power.
-/
noncomputable
def base (K : Type*) [field K] (v : valuation K ℤₘ₀) : ℝ≥0 :=
if 1 < nat.card (local_ring.residue_field v.valuation_subring)
  then nat.card (local_ring.residue_field v.valuation_subring)
  else 6

lemma one_lt_base (K : Type*) [field K] (v : valuation K ℤₘ₀) : 1 < base K v :=
begin
  rw base,
  split_ifs with hlt hge,
  { rw [nat.one_lt_cast], exact hlt },
  { norm_num }
end

lemma base_ne_zero (K : Type*) [field K] (v : valuation K ℤₘ₀) : base K v ≠ 0 :=
ne_zero_of_lt (one_lt_base K v)

end valuation

namespace discrete_valuation

open valuation ideal is_dedekind_domain multiplicative with_zero local_ring

variables {K : Type*} [field K] (v : valuation K ℤₘ₀)

/-When the valuation is defined on a field instead that simply on a (commutative) ring, we use the 
notion of `valuation_subring` instead of the weaker one of `integer`s.
-/
local notation `K₀` := v.valuation_subring

lemma uniformizer_of_associated {π₁ π₂ : K₀} (h1 : is_uniformizer v π₁) (H : associated π₁ π₂) :
  is_uniformizer v π₂ :=
begin
  obtain ⟨u, hu⟩ := H,
  rwa [is_uniformizer_iff, ← hu, subring.coe_mul, ← units.val_eq_coe, valuation.map_mul, 
    (integer.is_unit_iff_valuation_eq_one u.1).mp u.is_unit, mul_one]
end

lemma associated_of_uniformizer {π₁ π₂ : uniformizer v} : associated π₁.1 π₂.1 :=
begin
  have hval : v ((↑π₁)⁻¹ * ↑π₂) = 1,
  simp only [uniformizer.val_eq_coe, valuation.map_mul, map_inv₀, is_uniformizer_iff.mp π₁.2,
    is_uniformizer_iff.mp π₂.2, of_add_neg, coe_inv, inv_inv, mul_inv_cancel, ne.def, coe_ne_zero,
    not_false_iff],
  let p : v.integer := ⟨(↑π₁)⁻¹ * ↑π₂, (valuation.mem_integer v _).mpr (le_of_eq hval)⟩,
  use ((integer.is_unit_iff_valuation_eq_one p).mpr hval).unit,
  apply_fun (coe : K₀ → K) using subtype.val_injective,
  simp only [subring.coe_mul, is_unit.unit_spec, set_like.coe_mk, uniformizer.val_eq_coe,
    ← mul_assoc, mul_inv_cancel (uniformizer_ne_zero v π₁.2), one_mul],
end

lemma pow_uniformizer {r : K₀} (hr : r ≠ 0) (π : uniformizer v) :
  ∃ n : ℕ, ∃ u : K₀ˣ, r = π.1^n * u :=
begin
  have hr₀ : v r ≠ 0,
  { rw [ne.def, zero_iff, subring.coe_eq_zero_iff], exact hr},
  set m := - (unzero hr₀).to_add with hm,
  have hm₀ : 0 ≤ m, 
  { rw [hm, right.nonneg_neg_iff, ← to_add_one, to_add_le, ← coe_le_coe, coe_unzero],
    exact r.2 },
  obtain ⟨n, hn⟩ := int.eq_coe_of_zero_le hm₀,
  use n,
  have hpow : v (π.1^(-m) * r) = 1, 
  { rw [valuation.map_mul, map_zpow₀, is_uniformizer_iff.mp π.2, of_add_neg, coe_inv, inv_zpow',
      neg_neg, ← with_zero.coe_zpow, ← int.of_add_mul, one_mul, of_add_neg, of_add_to_add, coe_inv,
      coe_unzero, inv_mul_cancel hr₀], },
  set a : K₀ := ⟨π.1^(-m )*r, by apply le_of_eq hpow⟩ with ha,
  have ha₀ : (↑a : K) ≠ 0, 
  { simp only [ha, neg_neg, set_like.coe_mk, ne.def],
    by_cases h0 : to_add (unzero hr₀) = 0,
    { rw [h0, zpow_zero, one_mul, subring.coe_eq_zero_iff], exact hr },
    { apply mul_ne_zero,
      { rw [ne.def, zpow_eq_zero_iff h0],
        exact uniformizer_ne_zero' v π},
      { rw [ne.def, subring.coe_eq_zero_iff], exact hr, }}},
  have h_unit_a : is_unit a,
  { exact integers.is_unit_of_one (integer.integers v) ((is_unit_iff_ne_zero).mpr ha₀) hpow },
  use h_unit_a.unit,
  ext,
  rw [is_unit.unit_spec, subring.coe_mul, subring.coe_pow, subtype.coe_mk, hn, ← mul_assoc, 
    zpow_neg, zpow_coe_nat, mul_inv_cancel, one_mul],
  apply pow_ne_zero,
  exact uniformizer_ne_zero' _ π,
end

/--This proof of the lemma does not need the valuation to be discrete, although the fact that a
uniformizer exists forces the condition.-/
lemma uniformizer_is_generator (π : uniformizer v) :
  maximal_ideal v.valuation_subring = ideal.span {π.1} :=
begin
  apply (maximal_ideal.is_maximal _).eq_of_le,
  { intro h,
    rw ideal.span_singleton_eq_top at h,
    apply uniformizer_not_is_unit v π.2 h },
  { intros x hx,
    by_cases hx₀ : x = 0,
    { simp only [hx₀, ideal.zero_mem] },
    { obtain ⟨n, ⟨u, hu⟩⟩ := pow_uniformizer v hx₀ π,
      have hn : not (is_unit x) := λ h, (maximal_ideal.is_maximal _).ne_top
        (eq_top_of_is_unit_mem _ hx h),
      replace hn : n ≠ 0 := λ h, by {rw [hu, h, pow_zero, one_mul] at hn, exact hn u.is_unit},
      simpa [ideal.mem_span_singleton, hu, is_unit.dvd_mul_right, units.is_unit] using
        dvd_pow_self _ hn }},
end

lemma is_uniformizer_is_generator {π : v.valuation_subring } (hπ : is_uniformizer v π) :
  maximal_ideal v.valuation_subring = ideal.span {π} :=
uniformizer_is_generator _ ⟨π, hπ⟩

lemma pow_uniformizer_is_pow_generator {π : uniformizer v} (n : ℕ) :
  (maximal_ideal v.valuation_subring) ^ n = ideal.span {π.1 ^ n} :=
by rw [← ideal.span_singleton_pow, uniformizer_is_generator]


variable [is_discrete v]

lemma exists_uniformizer : ∃ π : K₀, is_uniformizer v (π : K) := 
begin
  letI surj_v : is_discrete v, apply_instance,
  refine ⟨⟨(surj_v.surj (multiplicative.of_add (- 1 : ℤ) : ℤₘ₀)).some, _⟩, 
    (surj_v.surj (multiplicative.of_add (- 1 : ℤ) : ℤₘ₀)).some_spec⟩,
  rw [mem_valuation_subring_iff, (surj_v.surj (multiplicative.of_add (- 1 : ℤ) : ℤₘ₀)).some_spec],
  exact (le_of_lt of_add_neg_one_lt_one),
end

instance : nonempty (uniformizer v) := 
⟨⟨(exists_uniformizer v).some, (exists_uniformizer v).some_spec⟩⟩


lemma not_is_field : ¬ is_field K₀ :=
begin
  obtain ⟨π, hπ⟩ := exists_uniformizer v,
  rintros ⟨-, -, h⟩,
  have := uniformizer_ne_zero v hπ,
  simp only [uniformizer_ne_zero v hπ, ne.def, subring.coe_eq_zero_iff] at this,
  specialize h this,
  rw ← is_unit_iff_exists_inv at h,
  exact uniformizer_not_is_unit v hπ h,
end


lemma uniformizer_of_generator {r : K₀}
  (hr : maximal_ideal v.valuation_subring = ideal.span {r}) : is_uniformizer v r :=
begin
  have hr₀ : r ≠ 0,
  { intro h,
    rw [h, set.singleton_zero, span_zero] at hr,
    exact ring.ne_bot_of_is_maximal_of_not_is_field (maximal_ideal.is_maximal v.valuation_subring)
    (not_is_field v) hr },
  obtain ⟨π, hπ⟩ := exists_uniformizer v,
  obtain ⟨n, u, hu⟩ := pow_uniformizer v hr₀ ⟨π, hπ⟩,
  rw [uniformizer_is_generator v ⟨π, hπ⟩, span_singleton_eq_span_singleton] at hr,
  exact uniformizer_of_associated v hπ hr,
end

section rank_one

variables {K}

noncomputable instance is_rank_one : is_rank_one v := 
{ hom         := with_zero_mult_int_to_nnreal (base_ne_zero K v),
  strict_mono := with_zero_mult_int_to_nnreal_strict_mono (one_lt_base K v),
  nontrivial  := 
  begin
    obtain ⟨π, hπ⟩ := exists_uniformizer v,
    exact ⟨π, ne_of_gt (uniformizer_valuation_pos v hπ),
      ne_of_lt (uniformizer_valuation_lt_one v hπ)⟩,
  end }

lemma is_rank_one_hom_def :
  is_rank_one.hom v = with_zero_mult_int_to_nnreal (base_ne_zero K v) :=
rfl

end rank_one


-- lemma pow_uniformizer_of_pow_generator {r : K₀} (n : ℕ) 
--   (hr : (maximal_ideal v.valuation_subring) ^ n = ideal.span {r ^ n}) : is_uniformizer v r := 
-- begin
--   rw [← ideal.span_singleton_pow] at hr,sorry,
--   -- by rw [← ideal.span_singleton_pow, generator_of_uniformizer]
-- end


-- [FAE] refactor using the above four lemmas
lemma ideal_is_principal (I : ideal K₀) : I.is_principal:=
begin
  classical,
  have π := (uniformizer.nonempty v).some,
  by_cases hI : I = ⊥,
  {rw hI, exact bot_is_principal},
  { rw ← ne.def at hI,
    let P : ℕ → Prop := λ n, π.1^n ∈ I,
    have H : ∃ n, P n,
    { obtain ⟨x, ⟨hx_mem, hx₀⟩⟩ := submodule.exists_mem_ne_zero_of_ne_bot hI,
      obtain ⟨n, ⟨u, hu⟩⟩ := pow_uniformizer v hx₀ π,
      use n,
      simp_rw P,
      rwa [← mul_unit_mem_iff_mem I u.is_unit, ← hu] },
    let N := nat.find H,
    use π.1^N,
    ext r,
    split,
    { intro hr,
      by_cases hr₀ : r = 0,
      { rw hr₀, exact zero_mem _ },
      { obtain ⟨m, ⟨u, hu⟩⟩ := pow_uniformizer v hr₀ π,
        rw submodule_span_eq,
        rw mem_span_singleton',
        use u * π.1^(m - N),
        rw [mul_assoc, ← pow_add, nat.sub_add_cancel, mul_comm, hu],
        apply nat.find_min',
        simp_rw P,
        rwa [← mul_unit_mem_iff_mem I u.is_unit, ← hu] } },
    { intro hr,    
      rw [submodule_span_eq, mem_span_singleton'] at hr,
      obtain ⟨a, ha⟩ := hr,
      rw ← ha,
      exact I.mul_mem_left a (nat.find_spec H), }},
end

lemma integer_is_principal_ideal_ring : is_principal_ideal_ring K₀:= 
⟨λ I, ideal_is_principal v I⟩

-- This is Chapter I, Section 1, Proposition 1 in Serre's Local Fields (TODO: proper reference)
instance dvr_of_is_discrete : discrete_valuation_ring K₀ :=
begin
  haveI := integer_is_principal_ideal_ring v,
  exact ((discrete_valuation_ring.tfae K₀ (not_is_field v)).out 0 4).mpr (ideal_is_principal v _),
end

variables (A : Type*) [comm_ring A] [is_domain A] [discrete_valuation_ring A]

open is_dedekind_domain.height_one_spectrum 

def maximal_ideal : height_one_spectrum A :=
{ as_ideal := maximal_ideal A,
  is_prime := ideal.is_maximal.is_prime (maximal_ideal.is_maximal A),
  ne_bot   := begin
    rw [ne.def, ← is_field_iff_maximal_ideal_eq],
    exact discrete_valuation_ring.not_is_field A,
  end }

variable {A}

-- This gives problems
-- noncomputable instance {L : Type*} [field L] [algebra A L] [fraction_ring A]: valued L ℤₘ₀ := 
-- (maximal_ideal A).adic_valued

noncomputable instance : valued (fraction_ring A) ℤₘ₀ := 
(maximal_ideal A).adic_valued


instance : is_discrete (@valued.v (fraction_ring A) _ ℤₘ₀ _ _) :=
is_discrete_of_exists_uniformizer valued.v
  (valuation_exists_uniformizer (fraction_ring A) (maximal_ideal A)).some_spec

end discrete_valuation

namespace discretely_valued

open valuation discrete_valuation

variables (K : Type*) [field K] [hv : valued K ℤₘ₀] 

local notation `K₀` := hv.v.valuation_subring

def is_uniformizer := valuation.is_uniformizer hv.v

def uniformizer := valuation.uniformizer hv.v

instance [hv : valued K ℤₘ₀] [is_discrete hv.v] : nonempty (uniformizer K) := 
⟨⟨(exists_uniformizer hv.v).some, (exists_uniformizer hv.v).some_spec⟩⟩

end discretely_valued