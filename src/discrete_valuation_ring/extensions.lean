/-
Copyright (c) 2023 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import discrete_valuation_ring.discrete_norm
import for_mathlib.discrete_valuation_ring
import for_mathlib.ring_theory.valuation.int_polynomial
import for_mathlib.ring_theory.valuation.minpoly
import for_mathlib.field_theory.minpoly.normal

noncomputable theory

open add_subgroup discrete_valuation discrete_valuation.discrete_norm_extension function 
  multiplicative nnreal finite_dimensional minpoly polynomial subgroup valuation with_zero

open_locale discrete_valuation nnreal

namespace discrete_valuation

section complete

variables {K : Type*} [field K] [hv : valued K ℤₘ₀] [is_discrete hv.v] {L : Type*} [field L] 
  [algebra K L] [complete_space K] 

include hv

lemma map_mul_aux [finite_dimensional K L] (x y : Lˣ) : 
  valued.v ((minpoly K ((x : L) * ↑y)).coeff 0) ^ 
    (finrank K L / (minpoly K ((x : L) * ↑y)).nat_degree) = 
  valued.v ((minpoly K (x : L)).coeff 0) ^ (finrank K L / (minpoly K (x : L)).nat_degree) 
  * valued.v ((minpoly K (y : L)).coeff 0) ^ (finrank K L / (minpoly K (y : L)).nat_degree) :=
begin
  have h_alg : algebra.is_algebraic K L := algebra.is_algebraic_of_finite K L,
  have hinj : injective (with_zero_mult_int_to_nnreal (base_ne_zero K hv.v)),
  { exact (with_zero_mult_int_to_nnreal_strict_mono (one_lt_base K hv.v)).injective, },
  rw [← function.injective.eq_iff hinj, _root_.map_mul, ← units.coe_mul, map_pow_div,
    map_pow_div, map_pow_div, ← mul_rpow,
    rpow_eq_rpow_iff (nat.cast_ne_zero.mpr (ne_of_gt finrank_pos))],
  ext,
  rw [nnreal.coe_mul, coe_rpow, coe_rpow, coe_rpow, ← eq_root_zero_coeff h_alg,
    ← eq_root_zero_coeff h_alg, ← eq_root_zero_coeff h_alg, units.coe_mul, _root_.map_mul],
  apply_instance,
  apply_instance,
end

variables (K L) 
def pow_extension_on_units [finite_dimensional K L] : 
  Lˣ →* (multiplicative ℤ) :=
{ to_fun   := λ x, with_zero.unzero (valuation.unit_pow_ne_zero hv.v x),
  map_one' := by simp only [units.val_eq_coe, units.coe_one, one, polynomial.coeff_sub, 
    polynomial.coeff_X_zero, polynomial.coeff_one_zero, zero_sub, valuation.map_neg, 
    valuation.map_one, one_pow, unzero_coe],
  map_mul' := λ x y,
  begin
    have h_alg : algebra.is_algebraic K L := algebra.is_algebraic_of_finite K L,
    simp only [units.val_eq_coe, units.coe_mul],
    rw [← with_zero.coe_inj, with_zero.coe_mul, with_zero.coe_unzero, with_zero.coe_unzero, 
      with_zero.coe_unzero],
    exact map_mul_aux x y,
  end } 

lemma pow_extension_on_units_apply [finite_dimensional K L] (x : Lˣ) : 
  pow_extension_on_units K L x = with_zero.unzero (valuation.unit_pow_ne_zero hv.v x) :=
rfl

def exp_extension_on_units [finite_dimensional K L] : ℕ :=
int.nat_abs (int.subgroup_cyclic (map (pow_extension_on_units K L) ⊤).to_add_subgroup).some

variables {K L}

lemma exp_extension_on_units_generates_range' [finite_dimensional K L] : 
  to_add_subgroup (map (pow_extension_on_units K L) ⊤) =
    closure {(exp_extension_on_units K L : ℤ)} := 
by rw [(int.subgroup_cyclic (map (pow_extension_on_units K L) 
  ⊤).to_add_subgroup).some_spec, ← zmultiples_eq_closure, ← zmultiples_eq_closure, 
  exp_extension_on_units, int.zmultiples_nat_abs]

lemma exp_extension_on_units_ne_zero [finite_dimensional K L] : exp_extension_on_units K L ≠ 0 :=
begin
  have h_alg : algebra.is_algebraic K L := algebra.is_algebraic_of_finite K L,
  obtain ⟨x, hx⟩ := exists_uniformizer hv.v,
  have hx_unit : is_unit (x : K),
  { exact is_unit_iff_ne_zero.mpr (uniformizer_ne_zero hv.v hx) },
  set z : Lˣ := units.map (algebra_map K L).to_monoid_hom (is_unit.unit hx_unit) with hz,
  rw is_uniformizer at hx,
  by_contradiction h0,
  have h := exp_extension_on_units_generates_range',
  rw [h0, zmod.nat_cast_self, closure_singleton_zero, _root_.map_eq_bot_iff,
    subgroup.map_eq_bot_iff, top_le_iff] at h,
  have hz1 : pow_extension_on_units K L z = 1,
  { rw [← monoid_hom.mem_ker, h], exact mem_top _ },
  have hzne1 : pow_extension_on_units K L z ≠ 1,
  { have hv : valued.v ((minpoly K ((units.map (algebra_map K L).to_monoid_hom) 
    hx_unit.unit).val).coeff 0) = valued.v (x : K),
    { rw [ring_hom.to_monoid_hom_eq_coe, units.val_eq_coe, units.coe_map, 
        is_unit.unit_spec, ring_hom.coe_monoid_hom, valuation.coeff_zero] },
    rw [hz, pow_extension_on_units_apply, ne.def, ← with_zero.coe_inj, coe_unzero, hv, hx,
      ← of_add_neg_nat, ← of_add_zero, with_zero.coe_inj, ring_hom.to_monoid_hom_eq_coe, 
      units.val_eq_coe, units.coe_map, is_unit.unit_spec, ring_hom.coe_monoid_hom, int.coe_nat_div,
      of_add_neg, of_add_zero, inv_eq_one, of_add_eq_one, ← int.coe_nat_div, int.coe_nat_eq_zero,
      nat.div_eq_zero_iff (minpoly.nat_degree_pos (is_algebraic_iff_is_integral.mp (h_alg _)))],
    exact not_lt.mpr (minpoly.nat_degree_le (is_algebraic_iff_is_integral.mp (h_alg _))) },
  exact hzne1 hz1,
end

variables (K L)

lemma exp_extension_on_units_pos [finite_dimensional K L] : 0 < exp_extension_on_units K L := 
nat.pos_of_ne_zero exp_extension_on_units_ne_zero

variables {K L}

-- This proof is ridiculous (TODO: golf)
lemma exp_extension_on_units_generates_range [finite_dimensional K L] :
  (map (pow_extension_on_units K L) ⊤) = 
    closure {of_add (exp_extension_on_units K L : ℤ)} :=
begin
  have h' : to_subgroup (to_add_subgroup (map (pow_extension_on_units K L) ⊤)) =
      to_subgroup (closure {(exp_extension_on_units K L : ℤ)}),
  { rw exp_extension_on_units_generates_range', },
  convert h',
  { ext x,
    have hx : x ∈ zpowers (of_add (exp_extension_on_units K L : ℤ)) ↔ 
    x ∈ (zpowers (of_add (exp_extension_on_units K L : ℤ)) : set (multiplicative ℤ)),
    { refl },
    have hx' : x ∈ (to_subgroup (closure {(exp_extension_on_units K L : ℤ)})) ↔
      x.to_add ∈ (add_subgroup.closure {(exp_extension_on_units K L : ℤ)}),
    { simp only [to_subgroup, rel_iso.coe_fn_mk, equiv.coe_fn_mk,
        add_submonoid.to_submonoid, coe_to_add_submonoid],
      rw ← subgroup.mem_carrier,
      change x ∈ to_add ⁻¹' (↑(add_subgroup.closure {(exp_extension_on_units K L : ℤ)}) : set ℤ)
      ↔ to_add x ∈ add_subgroup.closure {(exp_extension_on_units K L : ℤ)},
      rw set.mem_preimage,
      refl,},
    have hx'' : x ∈ of_add '' (zmultiples (exp_extension_on_units K L : ℤ) : set ℤ) ↔
      x.to_add ∈ ↑(zmultiples (exp_extension_on_units K L : ℤ)),
    { simp only [set.mem_image, set_like.mem_coe],
      split,
      { rintros ⟨n, hn, hnx⟩, rw ← hnx, exact hn, },
      { intro h, exact ⟨to_add x, h, rfl⟩, }, },
    rw [subgroup.mem_closure_singleton, ← mem_zpowers_iff, hx,
      ← of_add_image_zmultiples_eq_zpowers_of_add, hx', hx'', 
      add_subgroup.mem_closure_singleton, ← mem_zmultiples_iff],
    refl, },
end

variable (K)

lemma exists_mul_exp_extension_on_units [finite_dimensional K L] (x : Lˣ) : 
  ∃ (n : ℤ), (((of_add (-1 : ℤ))^n)^(exp_extension_on_units K L) : ℤₘ₀) =
  (valued.v ((minpoly K (x : L)).coeff 0))^((finrank K L)/((minpoly K (x : L)).nat_degree)) :=
begin
  set y := (with_zero.unzero (valuation.unit_pow_ne_zero hv.v x)),
  have h_mem : (with_zero.unzero (valuation.unit_pow_ne_zero hv.v x)) ∈ 
    subgroup.closure ({of_add (exp_extension_on_units K L : ℤ)} : set (multiplicative ℤ)),
  { rw [← exp_extension_on_units_generates_range, subgroup.mem_map],
    exact ⟨x, mem_top x, rfl⟩ },
  rw subgroup.mem_closure_singleton at h_mem,
  obtain ⟨n, hn⟩ := h_mem,
  use - n,
  rw [with_zero.of_add_neg_one_pow_comm n, ← with_zero.coe_zpow, hn],
  exact with_zero.coe_unzero _,
end

variable (L)

lemma exp_extension_on_units_dvd [finite_dimensional K L] : 
  exp_extension_on_units K L ∣ finrank K L :=
begin
  have h_alg := algebra.is_algebraic_of_finite K L,
  obtain ⟨π, hπ⟩ := exists_uniformizer hv.v,
  set u : L := algebra_map K L (π : K) with hu_def,
  have hu0 : u ≠ 0,
  { rw [hu_def, ne.def, _root_.map_eq_zero],
    exact uniformizer_ne_zero hv.v hπ,},
  obtain ⟨n, hn⟩ := exists_mul_exp_extension_on_units K (is_unit_iff_ne_zero.mpr hu0).unit,
  have hu : ((is_unit_iff_ne_zero.mpr hu0).unit : L) = u := rfl,
  have hne_zero : ((minpoly K ((algebra_map K L) ↑π)).nat_degree : ℤ) ≠ 0,
  { rw [nat.cast_ne_zero, ← pos_iff_ne_zero],
    exact minpoly.nat_degree_pos (is_algebraic_iff_is_integral.mp (h_alg _)),},
  have h_dvd : ((minpoly K ((algebra_map K L) ↑π)).nat_degree : ℤ) ∣ (finrank K L),
  { exact int.coe_nat_dvd.mpr (minpoly.degree_dvd (is_algebraic_iff_is_integral.mp (h_alg _)))},
  rw [hu, hu_def, valuation.coeff_zero, is_uniformizer_iff.mp hπ, ← with_zero.coe_pow,
    ← with_zero.coe_zpow, ← with_zero.coe_pow, with_zero.coe_inj, ← zpow_coe_nat, ← zpow_mul, 
    ← zpow_coe_nat, of_add_pow_comm, of_add_pow_comm (-1)] at hn,
  simp only [zpow_neg, zpow_one, inv_inj] at hn,
  replace hn := of_add_inj hn,
  have hn0 : 0 ≤ n, 
  { refine nonneg_of_mul_nonneg_left _ (nat.cast_pos.mpr (exp_extension_on_units_pos K L)),
    rw hn,
    exact nat.cast_nonneg _ },
  rw [int.coe_nat_div, eq_comm, int.div_eq_iff_eq_mul_right hne_zero h_dvd] at hn,
  use (minpoly K ((algebra_map K L) ↑π)).nat_degree * n.to_nat,
  rw [mul_comm, ← @nat.cast_inj ℤ _, hn, nat.cast_mul, nat.cast_mul, int.to_nat_of_nonneg hn0, 
    mul_assoc],
end

variable {L}

def extension_def [finite_dimensional K L] : L → ℤₘ₀ :=
λ x, by classical; exact if hx : x = 0 then 0 else 
  (of_add (-1 : ℤ))^(exists_mul_exp_extension_on_units K  (is_unit_iff_ne_zero.mpr hx).unit).some

variable {K}

lemma extension_def_apply [finite_dimensional K L]  (x : L) :
extension_def K x = (if hx : x = 0 then 0 else 
  (of_add (-1 : ℤ))^(exists_mul_exp_extension_on_units K (is_unit_iff_ne_zero.mpr hx).unit).some) :=
rfl

lemma extension_def_mul [finite_dimensional K L] (x y : L) :
  extension_def K (x * y) = extension_def K x * extension_def K y :=
begin
  have h_alg : algebra.is_algebraic K L := algebra.is_algebraic_of_finite K L,
  by_cases hx : x = 0,
  { have hxy : x * y = 0,
    { rw [hx, zero_mul] },
    rw [extension_def_apply, dif_pos hxy, extension_def_apply, dif_pos hx, zero_mul] },
    { by_cases hy : y = 0,
      { have hxy : x * y = 0,
        { rw [hy, mul_zero] },
        simp only [extension_def_apply],
        rw [dif_pos hxy, dif_pos hy, mul_zero] },
      { have hxy : x * y ≠ 0,
        { exact mul_ne_zero hx hy, },
        simp only [extension_def_apply],
        rw [dif_neg hx, dif_neg hy, dif_neg (mul_ne_zero hx hy)],
        have hinj : injective (with_zero_mult_int_to_nnreal (base_ne_zero K hv.v)),
        { exact (with_zero_mult_int_to_nnreal_strict_mono (one_lt_base K hv.v)).injective },
        rw [← function.injective.eq_iff hinj, ← pow_left_inj _ _ (exp_extension_on_units_pos K L), 
          ← nnreal.coe_eq, _root_.map_mul, mul_pow, ← _root_.map_pow,
          (exists_mul_exp_extension_on_units K (is_unit_iff_ne_zero.mpr hxy).unit).some_spec, 
          nnreal.coe_mul],
        nth_rewrite 1 ← _root_.map_pow,
        rw (exists_mul_exp_extension_on_units K (is_unit_iff_ne_zero.mpr hx).unit).some_spec,
        nth_rewrite 2 ← _root_.map_pow,
        rw [(exists_mul_exp_extension_on_units K (is_unit_iff_ne_zero.mpr hy).unit).some_spec, 
          _root_.map_pow, nnreal.coe_pow, ← pow_eq_pow_root_zero_coeff h_alg, 
          _root_.map_pow, nnreal.coe_pow, ← pow_eq_pow_root_zero_coeff h_alg, _root_.map_pow, 
          nnreal.coe_pow, ← pow_eq_pow_root_zero_coeff h_alg, ← mul_pow, ← mul h_alg],
        refl,
        repeat { exact minpoly.degree_dvd (is_algebraic_iff_is_integral.mp (h_alg _))},
        { exact zero_le' },
        { exact zero_le' }}},
end

variables (K L)

--set_option trace.class_instances true
def extension [finite_dimensional K L] : valuation L ℤₘ₀ := 
{ to_fun    := extension_def K,
  map_zero' := by rw [extension_def_apply, dif_pos rfl],
  map_one'  := 
  begin
    rw [extension_def_apply, dif_neg one_ne_zero],
    have h1 : (1 : L) ≠ 0 := one_ne_zero, 
    set u := (exists_mul_exp_extension_on_units K (is_unit_iff_ne_zero.mpr h1).unit).some 
      with hu_def,
    have hu : (↑(of_add (-1 : ℤ)) ^ u) ^ exp_extension_on_units K L = 
      valued.v ((minpoly K ↑((is_unit_iff_ne_zero.mpr h1).unit)).coeff 0) ^ 
        (finrank K L / (minpoly K ((is_unit_iff_ne_zero.mpr h1).unit : L)).nat_degree) := 
    (exists_mul_exp_extension_on_units K (is_unit_iff_ne_zero.mpr h1).unit).some_spec,
    simp only [is_unit.unit_spec, one, 
      coeff_sub, coeff_X_zero, coeff_one_zero, zero_sub, valuation.map_neg, valuation.map_one, 
      one_pow, inv_eq_one] at hu,
    simp only [← with_zero.coe_one, ← of_add_zero, ← with_zero.coe_zpow, 
      ← with_zero.coe_pow, with_zero.coe_inj, ← zpow_coe_nat, ← int.of_add_mul] at hu,
    have hu' := int.eq_zero_or_eq_zero_of_mul_eq_zero hu,
    rw or_eq_of_eq_false_right at hu',
    rw [← hu_def, ← with_zero.coe_one, ← of_add_zero, ← with_zero.coe_zpow, with_zero.coe_inj, 
      ← int.of_add_mul, hu'],
    { simp only [exp_extension_on_units_ne_zero, nat.cast_eq_zero] },
    { exact ne_zero.one L },
  end,
  map_mul'  := extension_def_mul,
  map_add_le_max' := λ x y,
  begin
    have h_alg : algebra.is_algebraic K L := algebra.is_algebraic_of_finite K L,
    by_cases hx : x = 0,
    { have hxy : x + y = y,
      { rw [hx, zero_add] },
      simp only [extension_def_apply, dif_pos hx, hxy],
      rw max_eq_right, 
      exact le_refl _,
      { exact zero_le' }},
    { by_cases hy : y = 0,
      { have hxy : x + y = x,
        { rw [hy, add_zero] },
          simp only [extension_def_apply, dif_pos hy, hxy],
          rw max_eq_left, 
          exact le_refl _,
        { exact zero_le' }},
      { by_cases hxy : x + y = 0,
        { simp only [extension_def_apply, dif_pos hxy, zero_le'] },
        { simp only [extension_def_apply, dif_neg hx, dif_neg hy, dif_neg hxy],
          set ux := (exists_mul_exp_extension_on_units K (is_unit_iff_ne_zero.mpr hx).unit).some 
            with hux_def,
          set uy := (exists_mul_exp_extension_on_units K (is_unit_iff_ne_zero.mpr hy).unit).some 
            with huy_def,
          set uxy := (exists_mul_exp_extension_on_units K (is_unit_iff_ne_zero.mpr hxy).unit).some 
            with huxy_def,
          rw [← hux_def, ← huy_def, ← huxy_def],
        rw _root_.le_max_iff,
        simp only [← with_zero.coe_zpow, coe_le_coe],
        have hd : 0 < (exp_extension_on_units K L: ℤ), 
        { rw [int.coe_nat_pos],
          exact nat.pos_of_ne_zero exp_extension_on_units_ne_zero, },
        rw [← zpow_le_zpow_iff' hd, zpow_coe_nat, zpow_coe_nat, ← coe_le_coe, 
          with_zero.coe_pow, with_zero.coe_zpow,
          (exists_mul_exp_extension_on_units K (is_unit_iff_ne_zero.mpr hxy).unit).some_spec],
        rw [ with_zero.coe_pow, with_zero.coe_zpow,
          (exists_mul_exp_extension_on_units K (is_unit_iff_ne_zero.mpr hx).unit).some_spec],
        rw [← zpow_le_zpow_iff' hd,zpow_coe_nat, zpow_coe_nat],
        nth_rewrite 1 [← coe_le_coe],
        simp only [with_zero.coe_pow, with_zero.coe_zpow,
          (exists_mul_exp_extension_on_units K (is_unit_iff_ne_zero.mpr hxy).unit).some_spec,
          (exists_mul_exp_extension_on_units K (is_unit_iff_ne_zero.mpr hy).unit).some_spec],
        simp only [← (with_zero_mult_int_to_nnreal_strict_mono 
          (one_lt_base K hv.v)).le_iff_le, ← nnreal.coe_le_coe],
        rw [_root_.map_pow, nnreal.coe_pow, ← real.rpow_nat_cast, nat.cast_div,
          ← pow_eq_pow_root_zero_coeff' h_alg], --x + y
        rw [_root_.map_pow, nnreal.coe_pow, ← real.rpow_nat_cast _
          (finrank K L / (minpoly K _).nat_degree), nat.cast_div,
          ← pow_eq_pow_root_zero_coeff' h_alg], -- x
        rw [_root_.map_pow, nnreal.coe_pow, ← real.rpow_nat_cast _
          (finrank K L / (minpoly K _).nat_degree), nat.cast_div,
          ← pow_eq_pow_root_zero_coeff' h_alg], -- y
        have h_le : (discrete_norm_extension h_alg) (x + y)  ≤ (discrete_norm_extension h_alg) x ∨ 
          (discrete_norm_extension h_alg) (x + y)  ≤ (discrete_norm_extension h_alg) y,
        { rw ← _root_.le_max_iff,
          exact (is_nonarchimedean h_alg) _ _ },
        cases h_le with hlex hley,
        { left,
          exact pow_le_pow_of_le_left (nonneg h_alg _) hlex _ },
        { right,
          exact pow_le_pow_of_le_left (nonneg h_alg _) hley _ },
        repeat { exact minpoly.degree_dvd (is_algebraic_iff_is_integral.mp (h_alg _))},
        repeat { rw nat.cast_ne_zero,
          exact ne_of_gt (minpoly.nat_degree_pos (is_algebraic_iff_is_integral.mp (h_alg _))) }}}}
  end }

namespace extension

variables {K L}

lemma apply [finite_dimensional K L] (x : L) : 
   extension K L x = (if hx : x = 0 then 0 else (of_add (-1 : ℤ))^
     (exists_mul_exp_extension_on_units K (is_unit_iff_ne_zero.mpr hx).unit).some) :=
rfl

lemma apply_if_neg [finite_dimensional K L] {x : L} (hx : x ≠ 0) :
  extension K L x = ((of_add (-1 : ℤ))^
    (exists_mul_exp_extension_on_units K (is_unit_iff_ne_zero.mpr hx).unit).some) :=
by rw [apply, dif_neg hx]

lemma le_one_iff_discrete_norm_extension_le_one [finite_dimensional K L] (x : L) :
  extension K L x ≤ (1 : ℤₘ₀) ↔ 
    discrete_norm_extension (algebra.is_algebraic_of_finite K L) x ≤ 1 :=
begin
  set h_alg := algebra.is_algebraic_of_finite K L,
  rw [apply],
  split_ifs with hx,
  { simp only [hx, _root_.map_zero, zero_le_one] },
  { have h_le_iff : discrete_norm_extension h_alg x ≤ 1 ↔ 
     (discrete_norm_extension h_alg x)^(finrank K L) ≤ 1,
    { rw pow_le_one_iff_of_nonneg (nonneg h_alg _)
        (ne_of_gt finrank_pos),
      repeat { apply_instance }},
    set n := (exists_mul_exp_extension_on_units K (is_unit_iff_ne_zero.mpr hx).unit).some 
      with hn_def,
    rw [← hn_def, h_le_iff, pow_eq_pow_root_zero_coeff _ _ (minpoly.degree_dvd 
      (is_algebraic_iff_is_integral.mp (h_alg x))), ← nnreal.coe_pow, ← _root_.map_pow],
    erw ← (exists_mul_exp_extension_on_units K (is_unit_iff_ne_zero.mpr hx).unit).some_spec,
    rw [← hn_def, ← nnreal.coe_one, nnreal.coe_le_coe, 
      ← _root_.map_one (with_zero_mult_int_to_nnreal (base_ne_zero K hv.v)),
      (with_zero_mult_int_to_nnreal_strict_mono (one_lt_base K hv.v)).le_iff_le,
      ← with_zero.coe_one, ← with_zero.coe_zpow, with_zero.coe_le_coe, ← with_zero.coe_pow, 
      with_zero.coe_le_coe, ← zpow_coe_nat, ← int.of_add_mul, ← int.of_add_mul, ← of_add_zero,
      of_add_le, of_add_le],
    exact ⟨λ h, mul_nonpos_of_nonpos_of_nonneg h (nat.cast_nonneg _), 
      λ h, nonpos_of_mul_nonpos_left h (nat.cast_pos.mpr (exp_extension_on_units_pos K L))⟩ }
end


variables (K L)

lemma exists_generating_unit [finite_dimensional K L] :
  ∃ (x : Lˣ), pow_extension_on_units K L x = of_add (-exp_extension_on_units K L : ℤ) :=
begin
  have h_mem : of_add (exp_extension_on_units K L : ℤ) ∈ 
    subgroup.closure {of_add (exp_extension_on_units K L : ℤ)},
  { exact subgroup.mem_closure_singleton.mpr ⟨1, by rw zpow_one⟩,},
  rw [← exp_extension_on_units_generates_range, subgroup.mem_map] at h_mem,
  obtain ⟨x, _, hx⟩ := h_mem,
  use x⁻¹,
  rw [map_inv, hx],
  refl,
end

instance is_discrete_of_finite [finite_dimensional K L]  :
  is_discrete (extension K L) := 
begin
  set x := (exists_generating_unit K L).some,
  have hx := (exists_generating_unit K L).some_spec,
  rw ←  with_zero.coe_inj at hx,
  simp only [pow_extension_on_units, units.val_eq_coe, monoid_hom.coe_mk, coe_unzero,
    of_add_neg_nat] at hx,
  have hπ1 : extension K L x = (multiplicative.of_add (-1 : ℤ)),
  { rw [extension.apply_if_neg, ← with_zero.zpow_left_inj _ with_zero.coe_ne_zero 
      (nat.cast_ne_zero.mpr exp_extension_on_units_ne_zero)],
    { have hx0 : (x : L) ≠ 0, { exact units.ne_zero _ },
      rw [zpow_coe_nat, zpow_coe_nat, ← hx],
      erw (exists_mul_exp_extension_on_units K x).some_spec,
      refl, },
    { exact zpow_ne_zero _ with_zero.coe_ne_zero,
    exact units.ne_zero _ }},
  set π : (extension K L).valuation_subring := ⟨(exists_generating_unit K L).some, 
    by rw [mem_valuation_subring_iff, hπ1]; exact le_of_lt with_zero.of_add_neg_one_lt_one⟩, 
  have hπ : extension K L (π : L) = (multiplicative.of_add (-1 : ℤ)) := hπ1,
  apply is_discrete_of_exists_uniformizer (extension K L) hπ,
end

variables {K L}

-- TODO: Maybe this can be an instance. Update: probably not 
-- (because of h_alg, plus the linter complains)
@[protected] def uniform_space (h_alg : algebra.is_algebraic K L) : 
  uniform_space L := 
discretely_normed_field_extension_uniform_space h_alg

variables (K L)

-- TODO: Diamond?
@[protected] def normed_field [finite_dimensional K L] : normed_field L :=
begin
  have h_alg := algebra.is_algebraic_of_finite K L,
  letI : nontrivially_normed_field K := nontrivially_discretely_normed_field K,
  exact spectral_norm_to_normed_field h_alg (norm_is_nonarchimedean K),
end

.

@[protected] def valued [finite_dimensional K L] : valued L ℤₘ₀ := --valued.mk' (w 𝔽_[p]⟮⟮X⟯⟯ K)
begin
  letI : normed_field L := normed_field K L,
  exact { v := extension K L,
  is_topological_valuation := λ U,
  begin
    rw metric.mem_nhds_iff,
    refine ⟨λ h, _, λ h, _⟩, 
    { obtain ⟨ε, hε, h⟩ := h,
      obtain ⟨δ, hδ⟩ := real.exists_strict_mono_lt 
        (with_zero_mult_int_to_nnreal_strict_mono (one_lt_base K hv.v)) hε,
      use δ ^(finrank K L / (exp_extension_on_units K L)),
      intros x hx,
      simp only [set.mem_set_of_eq, extension.apply] at hx,
      apply h,
      rw [mem_ball_zero_iff], 
      split_ifs at hx with h0 h0,
      { rw [h0, norm_zero], exact hε },
      { set n := (exists_mul_exp_extension_on_units K (is_unit_iff_ne_zero.mpr h0).unit).some 
          with hn_def,
        set hn := (exists_mul_exp_extension_on_units K (is_unit_iff_ne_zero.mpr h0).unit).some_spec,
        have hpos : 0 < (exp_extension_on_units K L : ℝ),
        { exact nat.cast_pos.mpr (exp_extension_on_units_pos K L), },
        have hpos' : 0 < (finrank K L : ℝ),
        { exact nat.cast_pos.mpr finrank_pos },
        have h_alg := algebra.is_algebraic_of_finite K L,
        rw ← hn_def at hx, 
        have hx' := real.rpow_lt_rpow (nnreal.coe_nonneg _)
          ((with_zero_mult_int_to_nnreal_strict_mono (one_lt_base K hv.v)) hx) hpos,
        rw [real.rpow_nat_cast, ← nnreal.coe_pow, ← _root_.map_pow, hn, _root_.map_pow, 
          nnreal.coe_pow, ← discrete_norm_extension.pow_eq_pow_root_zero_coeff h_alg _
            (minpoly.degree_dvd (is_algebraic_iff_is_integral.mp 
            (h_alg ↑((is_unit_iff_ne_zero.mpr h0).unit))))] at hx',
        rw [← real.rpow_lt_rpow_iff (norm_nonneg _) (le_of_lt hε) hpos', real.rpow_nat_cast],
        apply lt_trans hx',
        rw [units.coe_pow, _root_.map_pow, nnreal.coe_pow, real.rpow_nat_cast, ← pow_mul,
          nat.div_mul_cancel (exp_extension_on_units_dvd K L), ← real.rpow_nat_cast,
          real.rpow_lt_rpow_iff (nnreal.coe_nonneg _) (le_of_lt hε) hpos'],
        exact hδ, }},
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
  ..(uniform_space (algebra.is_algebraic_of_finite K L)),
  ..non_unital_normed_ring.to_normed_add_comm_group}
end

#exit

@[protected, priority 100] instance complete_space [finite_dimensional K L] : 
  @complete_space L (uniform_space (algebra.is_algebraic_of_finite K L)) := 
begin
  letI : nontrivially_normed_field K := nontrivially_discretely_normed_field K,
  exact spectral_norm_complete_space (algebra.is_algebraic_of_finite K L) 
    (norm_is_nonarchimedean K),
end

@[protected] lemma is_complete [finite_dimensional K L] : 
  @is_complete L (uniform_space (algebra.is_algebraic_of_finite K L)) set.univ := 
begin
  rw ← complete_space_iff_is_complete_univ,
  apply_instance,
end

variables {K L}

lemma le_one_of_integer [fr : is_fraction_ring hv.v.valuation_subring K] 
  [finite_dimensional K L] (x : (integral_closure hv.v.valuation_subring L)) : 
  extension K L (x : L) ≤ 1 :=
begin
  letI : is_fraction_ring hv.v.valuation_subring.to_subring K := fr,
  exact (extension.le_one_iff_discrete_norm_extension_le_one _).mpr (le_one_of_integer _ x)
end

variables (K L)

lemma integral_closure_eq_integer [is_fraction_ring hv.v.valuation_subring K] 
  [finite_dimensional K L] :
  (integral_closure hv.v.valuation_subring L).to_subring = 
    (extension K L).valuation_subring.to_subring :=
begin
  classical,
  have h_alg : algebra.is_algebraic K L := algebra.is_algebraic_of_finite K L,
  ext x,
  have h : x ∈ (integral_closure hv.v.valuation_subring L) ↔ is_integral hv.v.valuation_subring x,
  { refl }, --TODO: mathlib lemma
  simp only [subalgebra.mem_to_subring, valuation_subring.mem_to_subring, 
    mem_valuation_subring_iff, h, is_integral, ring_hom.is_integral_elem],
  refine ⟨λ hx, le_one_of_integer ⟨x, hx⟩, λ hx, _⟩,
  { rw extension.le_one_iff_discrete_norm_extension_le_one at hx,
    let q := minpoly K x,
      have hq : ∀ n : ℕ, (q.coeff n) ∈ hv.v.valuation_subring,
      { exact (le_one_iff_integral_minpoly _ _).mp hx, },
      set p : polynomial (hv.v.valuation_subring) := int_polynomial hv.v hq,
      refine⟨int_polynomial hv.v hq, (int_polynomial.monic_iff hv.v hq).mpr
        (minpoly.monic (is_algebraic_iff_is_integral.mp (h_alg x))), 
        by rw [int_polynomial.eval₂_eq, minpoly.aeval]⟩ }
end

end extension

open extension

namespace integral_closure

--Chapter 2, Section 2, Proposition 3 in Serre's Local Fields
instance discrete_valuation_ring_of_finite_extension [finite_dimensional K L] : 
  discrete_valuation_ring (integral_closure hv.v.valuation_subring L) := 
begin
  letI hw : valued L ℤₘ₀ := valued.mk' (extension K L),
  letI hw_disc : is_discrete hw.v := extension.is_discrete_of_finite K L,
  let e : (extension K L).valuation_subring ≃+* (integral_closure hv.v.valuation_subring L) :=
  ring_equiv.subring_congr (integral_closure_eq_integer K L).symm,
  exact ring_equiv.discrete_valuation_ring e,
end

--FROM NOW ON WE SHOULD THINK IF WE WANT TO KEEP THESE RESULTS

lemma finrank_eq : finite_dimensional.finrank hv.v.valuation_subring 
  (integral_closure hv.v.valuation_subring L) = finite_dimensional.finrank K L :=
sorry

end integral_closure

variables [finite_dimensional K L] 

local notation `K₀` := hv.v.valuation_subring
local notation `L₀` := (extension K L).valuation_subring

def valuation_subring.algebra [is_fraction_ring K₀ K] : algebra K₀ L₀ :=
begin
  have h : algebra hv.v.valuation_subring (extension K L).valuation_subring.to_subring,
  { rw ← integral_closure_eq_integer,
    exact (integral_closure ↥(valued.v.valuation_subring) L).algebra},
  exact h,
end

end complete

end discrete_valuation