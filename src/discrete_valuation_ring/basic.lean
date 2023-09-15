import ring_theory.dedekind_domain.adic_valuation
import ring_theory.dedekind_domain.pid
import ring_theory.discrete_valuation_ring.basic
import ring_theory.ideal.basic
import ring_theory.valuation.valuation_subring
import topology.algebra.valued_field
import topology.algebra.with_zero_topology
import for_mathlib.rank_one_valuation
import for_mathlib.with_zero
import for_mathlib.ring_theory.valuation.integers

/-!
# Discrete Valuation Rings

In this file we prove basic results about Discrete Valuation Rings, building on the main definitions
provided in `ring_theory.discrete_valuation_ring.basic`. We focus in particular on discrete
valuations and on `valued` structures on the field of fractions of a DVR, as well as on a DVR
structure on the unit ball of a `valued` field whose valuation is discrete.

## Main Definitions
* `is_discrete`: We define a valuation to be discrete if it is ℤₘ₀-valued and surjective.
* `is_uniformizer`: Given a ℤₘ₀-valued valuation `v` on a ring `R`, an element `π : R` is a
  uniformizer if `v π = multiplicative.of_add (- 1 : ℤ) : ℤₘ₀`.
* `uniformizer`: A strucure bundling an element of a ring and a proof that it is a uniformizer.
* `base`: Given a valued field `K`, if the residue field of its unit ball (that is a local field)
  is finite, then `valuation_base` is the cardinal of the residue field, and otherwise it takes the
  value `6` which  is not a prime power.
* The `instance dvr_of_is_discrete` is the formalization of Chapter I, Section 1, Proposition 1 in
  Serre's **Local Fields** showing that the unit ball of a discretely-valued field is a DVR.


## Main Results
* `associated_of_uniformizer` An element associated to a uniformizer is itself a uniformizer
* `uniformizer_of_associated` If two elements are uniformizers, they are associated.
* `is_uniformizer_is_generator` A generator of the maximal ideal is a uniformizer if the valuation
  is discrete.
* `is_discrete_of_exists_uniformizer` If there exists a uniformizer, the valuation is discrete.
* `exists_uniformizer_of_discrete` Conversely, if the valuation is discrete there exists a
  uniformizer.
* `is_uniformizer_of_generator` A uniformizer generates the maximal ideal.
* `discrete_valuation.is_discrete` Given a DVR, the valuation induced on its ring of fractions is
  discrete.
* `discrete_valuation.dvr_equiv_unit_ball` The ring isomorphism between a DVR and the unit ball in 
  its field of fractions endowed with the adic valuation of the maximal ideal.

## Implementation details
In the section `discrete_valuation` we put a `valued` instance only on `fraction_field A`, where
`A` is the DVR, and not on any field `L` such that `[is_fraction_field A L]` because this creates
loops in the type-class inference mechanism.
-/

open_locale discrete_valuation nnreal

open multiplicative

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

/-- We insist that `v` takes values in ℤₘ₀ in order to define uniformizers as the elements in `K`
whose valuation is exactly `with_zero.multiplicative (- 1) : ℤₘ₀`-/
class is_discrete (v : valuation A ℤₘ₀) : Prop :=
(surj : function.surjective v)

open valuation ideal multiplicative with_zero

variables {R : Type*} [comm_ring R] (vR : valuation R ℤₘ₀)

/-- An element `π : R` is a uniformizer if `v π = multiplicative.of_add (- 1 : ℤ) : ℤₘ₀`.-/
def is_uniformizer (π : R) : Prop := 
vR π = (multiplicative.of_add (- 1 : ℤ) : ℤₘ₀)

variable {vR}
lemma is_uniformizer_iff {π : R} : is_uniformizer vR π ↔ 
  vR π = (multiplicative.of_add (- 1 : ℤ) : ℤₘ₀) := refl _

variable (vR)

/-- The structure `uniformizer` bundles together the term in the ring and a proof that it is a
  uniformizer.-/
@[ext] structure uniformizer :=
(val : vR.integer)
(valuation_eq_neg_one : is_uniformizer vR val)

/-- A constructor for uniformizers.-/
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
otherwise it takes the value `6` which is not a prime power.-/
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

open valuation ideal /- is_dedekind_domain -/ multiplicative with_zero local_ring

variables {K : Type*} [field K] (v : valuation K ℤₘ₀)

/- When the valuation is defined on a field instead that simply on a (commutative) ring, we use the 
notion of `valuation_subring` instead of the weaker one of `integer`s to access the corresponding
API. -/

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

/-- This proof of the lemma does not need the valuation to be discrete, although the fact that a
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

lemma exists_uniformizer_of_discrete : ∃ π : K₀, is_uniformizer v (π : K) := 
begin
  letI surj_v : is_discrete v, apply_instance,
  refine ⟨⟨(surj_v.surj (multiplicative.of_add (- 1 : ℤ) : ℤₘ₀)).some, _⟩, 
    (surj_v.surj (multiplicative.of_add (- 1 : ℤ) : ℤₘ₀)).some_spec⟩,
  rw [mem_valuation_subring_iff, (surj_v.surj (multiplicative.of_add (- 1 : ℤ) : ℤₘ₀)).some_spec],
  exact (le_of_lt of_add_neg_one_lt_one),
end

instance : nonempty (uniformizer v) := 
⟨⟨(exists_uniformizer_of_discrete v).some, (exists_uniformizer_of_discrete v).some_spec⟩⟩


lemma not_is_field : ¬ is_field K₀ :=
begin
  obtain ⟨π, hπ⟩ := exists_uniformizer_of_discrete v,
  rintros ⟨-, -, h⟩,
  have := uniformizer_ne_zero v hπ,
  simp only [uniformizer_ne_zero v hπ, ne.def, subring.coe_eq_zero_iff] at this,
  specialize h this,
  rw ← is_unit_iff_exists_inv at h,
  exact uniformizer_not_is_unit v hπ h,
end

lemma is_uniformizer_of_generator {r : K₀}
  (hr : maximal_ideal v.valuation_subring = ideal.span {r}) : is_uniformizer v r :=
begin
  have hr₀ : r ≠ 0,
  { intro h,
    rw [h, set.singleton_zero, span_zero] at hr,
    exact ring.ne_bot_of_is_maximal_of_not_is_field (maximal_ideal.is_maximal v.valuation_subring)
    (not_is_field v) hr },
  obtain ⟨π, hπ⟩ := exists_uniformizer_of_discrete v,
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
    obtain ⟨π, hπ⟩ := exists_uniformizer_of_discrete v,
    exact ⟨π, ne_of_gt (uniformizer_valuation_pos v hπ),
      ne_of_lt (uniformizer_valuation_lt_one v hπ)⟩,
  end }

lemma is_rank_one_hom_def :
  is_rank_one.hom v = with_zero_mult_int_to_nnreal (base_ne_zero K v) :=
rfl

end rank_one

lemma ideal_is_principal (I : ideal K₀) : I.is_principal:=
begin
  suffices : (∀ (P : ideal K₀), P.is_prime → submodule.is_principal P),
  exact (is_principal_ideal_ring.of_prime this).principal I,
  intros P hP,
  by_cases h_ne_bot : P = ⊥,
  {rw h_ne_bot, exact bot_is_principal},
  { let π := (uniformizer.nonempty v).some,
    obtain ⟨x, ⟨hx_mem, hx₀⟩⟩ := submodule.exists_mem_ne_zero_of_ne_bot h_ne_bot,
    obtain ⟨n, ⟨u, hu⟩⟩ := pow_uniformizer v hx₀ π,
    by_cases hn : n = 0,
  { rw [hu, hn, pow_zero, one_mul] at hx_mem,
    exact (hP.ne_top (ideal.eq_top_of_is_unit_mem P hx_mem u.is_unit)).elim },
  { rw [hu, ideal.mul_unit_mem_iff_mem P u.is_unit, is_prime.pow_mem_iff_mem hP _
      (pos_iff_ne_zero.mpr hn), ← ideal.span_singleton_le_iff_mem, ← uniformizer_is_generator v π]
      at hx_mem,
    rw [← ideal.is_maximal.eq_of_le (local_ring.maximal_ideal.is_maximal K₀) hP.ne_top hx_mem],
    use ⟨π.1, uniformizer_is_generator v π⟩ } },
end

lemma integer_is_principal_ideal_ring : is_principal_ideal_ring K₀:= 
⟨λ I, ideal_is_principal v I⟩

/-- This is Chapter I, Section 1, Proposition 1 in Serre's Local Fields -/
instance dvr_of_is_discrete : discrete_valuation_ring K₀ :=
{ to_is_principal_ideal_ring := integer_is_principal_ideal_ring v,
  to_local_ring := infer_instance,
  not_a_field' := by rw [ne.def, ← is_field_iff_maximal_ideal_eq]; exact not_is_field v }

variables (A : Type*) [comm_ring A] [is_domain A] [discrete_valuation_ring A]

open is_dedekind_domain is_dedekind_domain.height_one_spectrum subring discrete_valuation_ring

/-- The maximal ideal of a DVR-/
def maximal_ideal : height_one_spectrum A :=
{ as_ideal := maximal_ideal A,
  is_prime := ideal.is_maximal.is_prime (maximal_ideal.is_maximal A),
  ne_bot   := by simpa [ne.def, ← is_field_iff_maximal_ideal_eq] using 
    discrete_valuation_ring.not_is_field A }

variable {A}

noncomputable instance : valued (fraction_ring A) ℤₘ₀ := (maximal_ideal A).adic_valued

instance : is_discrete valued.v :=
is_discrete_of_exists_uniformizer valued.v
  (valuation_exists_uniformizer (fraction_ring A) (maximal_ideal A)).some_spec

lemma exists_of_le_one {x : (fraction_ring A)} (H : valued.v x ≤ (1 : ℤₘ₀)) :
  ∃ a : A, (algebra_map A (fraction_ring A) a) = x :=
begin
  obtain ⟨π, hπ⟩ := exists_irreducible A,
  obtain ⟨a, ⟨b, ⟨hb, h_frac⟩⟩⟩ := @is_fraction_ring.div_surjective A _ _ _ _ _ _ x,
  by_cases ha : a = 0,
  { rw ← h_frac,
    use 0,
    rw [ha, _root_.map_zero, zero_div] },
  { rw ← h_frac at H,
    obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible ha hπ,
    obtain ⟨m, v, rfl⟩ := eq_unit_mul_pow_irreducible (non_zero_divisors.ne_zero hb) hπ,
    replace hb := (mul_mem_non_zero_divisors.mp hb).2,
    erw [mul_comm ↑v _, _root_.map_mul _ ↑u _, _root_.map_mul _ _ ↑v, div_eq_mul_inv, mul_assoc, 
      valuation.map_mul, valuation_one_of_is_unit u.is_unit, one_mul, mul_inv, ← mul_assoc, 
      valuation.map_mul, map_inv₀, valuation_one_of_is_unit v.is_unit, inv_one, mul_one, 
      ← div_eq_mul_inv, ← @is_fraction_ring.mk'_mk_eq_div _ _ _ (fraction_ring A) _ _ _ (π^n) _ hb,
      @valuation_of_mk' A _ _ _ (fraction_ring A) _ _ _ (maximal_ideal A) (π^n) ⟨π^m, hb⟩, 
      set_like.coe_mk, valuation.map_pow, valuation.map_pow] at H,
    have h_mn : m ≤ n,
    { have π_lt_one := (int_valuation_lt_one_iff_dvd (maximal_ideal A) π).mpr
        (dvd_of_eq ((irreducible_iff_uniformizer _).mp hπ)),
      rw ← int_valuation_apply at π_lt_one,
      have : (maximal_ideal A).int_valuation π ≠ 0 := int_valuation_ne_zero _ _ hπ.ne_zero,
      zify,
      rw ← sub_nonneg,
      rw [← coe_unzero this, ← with_zero.coe_one] at H π_lt_one,
      rw [div_eq_mul_inv, ← with_zero.coe_pow, ← with_zero.coe_pow, ← with_zero.coe_inv, 
        ← zpow_coe_nat, ← zpow_coe_nat, ← with_zero.coe_mul,with_zero.coe_le_coe, ← zpow_sub, 
        ← of_add_zero, ← of_add_to_add (unzero _ ^ (↑n - ↑m)), of_add_le, int.to_add_zpow] at H,
      apply nonneg_of_mul_nonpos_right H,
      rwa [← to_add_one, to_add_lt, ← with_zero.coe_lt_coe] },
    use u * π^(n-m) * v.2,
    simp only [← h_frac, units.inv_eq_coe_inv, _root_.map_mul, _root_.map_pow, map_units_inv,
      mul_assoc, mul_div_assoc ((algebra_map A _) ↑u) _ _],
    congr' 1,
    rw [div_eq_mul_inv, mul_inv, mul_comm ((algebra_map A _) ↑v)⁻¹ _,
      ← mul_assoc _ _ ((algebra_map A _) ↑v)⁻¹],
    congr,
    rw [pow_sub₀ _ _ h_mn],
    apply is_fraction_ring.to_map_ne_zero_of_mem_non_zero_divisors,
    rw mem_non_zero_divisors_iff_ne_zero,
    exacts [hπ.ne_zero, valuation_le_one (maximal_ideal A), valuation_le_one (maximal_ideal A)] }
end

lemma alg_map_eq_integers : subring.map (algebra_map A (fraction_ring A)) ⊤ =
  valued.v.valuation_subring.to_subring :=
begin
  ext,
  refine ⟨λ h, _, λ h, _⟩,
  { obtain ⟨_, _ , rfl⟩ := subring.mem_map.mp h,
    apply valuation_le_one },
  { obtain ⟨y, rfl⟩ := exists_of_le_one h,
    rw subring.mem_map,
    exact ⟨y, mem_top _, rfl⟩ },
end

/-- The ring isomorphism between a DVR and the unit ball in 
  its field of fractions endowed with the adic valuation of the maximal ideal.-/
noncomputable
definition dvr_equiv_unit_ball : A ≃+* (@valued.v (fraction_ring A) _ ℤₘ₀ _ _).valuation_subring :=
(top_equiv.symm).trans ((equiv_map_of_injective _ (algebra_map A (fraction_ring A))
  (is_fraction_ring.injective A _)).trans (ring_equiv.subring_congr alg_map_eq_integers ))


end discrete_valuation

namespace discretely_valued

open valuation discrete_valuation

variables (K : Type*) [field K] [hv : valued K ℤₘ₀] 

/-- The definition of being a uniformizer for an element of a valued field-/
def is_uniformizer := valuation.is_uniformizer hv.v

/-- The structure `uniformizer` for a valued field-/
definition uniformizer := valuation.uniformizer hv.v

instance [hv : valued K ℤₘ₀] [is_discrete hv.v] : nonempty (uniformizer K) := 
⟨⟨(exists_uniformizer_of_discrete hv.v).some, (exists_uniformizer_of_discrete hv.v).some_spec⟩⟩

end discretely_valued