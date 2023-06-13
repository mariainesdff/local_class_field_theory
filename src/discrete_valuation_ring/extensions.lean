import number_theory.ramification_inertia
import discrete_valuation_ring.basic
import from_mathlib.normed_valued
import for_mathlib.rank_one_valuation
import spectral_norm
import with_zero

noncomputable theory

open multiplicative valuation with_zero
open_locale discrete_valuation nnreal

namespace multiplicative

lemma of_add_pow_comm (a b : ℤ) : (of_add a)^b = (of_add b)^a :=
by rw [← int.of_add_mul, mul_comm, int.of_add_mul]

lemma of_add_inj {x y : multiplicative ℤ} (hxy : of_add x = of_add y) : x = y := hxy

end multiplicative

namespace with_zero
--TODO: rename
lemma of_add_zpow (n : ℤ) : (of_add n : ℤₘ₀) = (of_add (1 : ℤ))^n :=
by rw [← with_zero.coe_zpow, with_zero.coe_inj, ← int.of_add_mul, one_mul]

lemma of_add_pow_pow_comm (a b c : ℤ) : 
  ((of_add (a : ℤ) : ℤₘ₀) ^ b) ^ c =  ((of_add (a : ℤ)) ^ c) ^ b :=
begin
  simp only [ ← with_zero.coe_zpow],
  rw [← zpow_mul,  mul_comm, zpow_mul],
end

lemma of_add_neg_one_pow_comm (a : ℤ) (n : ℕ) : 
  ((of_add (-1 : ℤ) : ℤₘ₀) ^ (-a)) ^ n =  ((of_add (n : ℤ)) ^ a) :=
by rw [with_zero.of_add_zpow (-1), ← zpow_mul, neg_mul, one_mul, neg_neg, ← zpow_coe_nat,
  of_add_pow_pow_comm 1 a, ← with_zero.coe_zpow,  ← int.of_add_mul, one_mul]

end with_zero

namespace add_subgroup

lemma closure_singleton_eq_zmultiples {A : Type*} [add_group A] (a : A) :
  closure {a} = zmultiples a :=
by ext n; rw [mem_closure_singleton, mem_zmultiples_iff]

end add_subgroup

namespace minpoly

theorem degree_dvd {K : Type*} [field K] {L : Type*} [field L] [algebra K L] {x : L}
  [finite_dimensional K L] (hx : is_integral K x) :
  (minpoly K x).nat_degree ∣ (finite_dimensional.finrank K L) :=
begin
  rw [dvd_iff_exists_eq_mul_left, ← intermediate_field.adjoin.finrank hx],
  use finite_dimensional.finrank ↥K⟮x⟯ L,
  rw [eq_comm, mul_comm],
  exact finite_dimensional.finrank_mul_finrank _ _ _,
end

end minpoly

section is_rank_one

variables {K : Type*} [field K] 

def is_rank_one_of_is_discrete (v : valuation K ℤₘ₀) [is_discrete v] {e : ℝ≥0} (he0 : e ≠ 0) 
  (he1 : 1 < e) : is_rank_one v :=
{ hom         := with_zero_mult_int_to_nnreal he0,
  strict_mono := with_zero_mult_int_to_nnreal_strict_mono he1,
  nontrivial  := 
  begin
    obtain ⟨π, hπ⟩ := exists_uniformizer v,
    exact ⟨π, ne_of_gt (uniformizer_valuation_pos v hπ),
      ne_of_lt (uniformizer_valuation_lt_one v hπ)⟩,
  end }

end is_rank_one

namespace discrete_valuation

-- TODO: I think these could be moved to dvr.basic
def valuation_base (K : Type*) [field K] [hv : valued K ℤₘ₀] [is_discrete hv.v] : ℝ≥0 :=
if 1 < nat.card (local_ring.residue_field hv.v.valuation_subring)
  then nat.card (local_ring.residue_field hv.v.valuation_subring)
  else 6

lemma one_lt_valuation_base (K : Type*) [field K] [hv : valued K ℤₘ₀] [is_discrete hv.v] : 
  1 < valuation_base K :=
begin
  rw valuation_base,
  split_ifs with hlt hge,
  { rw [nat.one_lt_cast], exact hlt },
  { norm_num }
end

lemma valuation_base_ne_zero (K : Type*) [field K] [hv : valued K ℤₘ₀] [is_discrete hv.v] : 
  valuation_base K ≠ 0 :=
ne_zero_of_lt (one_lt_valuation_base K)

end discrete_valuation

section extension

open finite_dimensional minpoly discrete_valuation

variables (K : Type*) [field K] [hv : valued K ℤₘ₀]

section is_discrete

variables [is_discrete hv.v] 

instance rk1 : is_rank_one hv.v := is_rank_one_of_is_discrete hv.v (valuation_base_ne_zero K) 
  (one_lt_valuation_base K)

include hv

@[priority 100] def disc_norm_field : normed_field K :=
rank_one_valuation.valued_field.to_normed_field K ℤₘ₀

--local attribute [priority 100, instance] disc_norm_field

@[priority 100] def disc_norm_field' : nontrivially_normed_field K :=
{ non_trivial := 
  begin
    obtain ⟨x, hx⟩ := exists_uniformizer hv.v,
    use x.1⁻¹,
    erw [@norm_inv K (@normed_field.to_normed_division_ring K (disc_norm_field K)),
      one_lt_inv_iff, rank_one_valuation.norm_lt_one_iff_val_lt_one,
      rank_one_valuation.norm_pos_iff_val_pos],
    exact ⟨uniformizer_valuation_pos hv.v hx, uniformizer_valuation_lt_one hv.v hx⟩,
  end
  ..(@rank_one_valuation.valued_field.to_normed_field K _ ℤₘ₀ _ _ (rk1 K))  } 

local attribute [priority 100, instance] disc_norm_field'

lemma norm_is_nonarchimedean : is_nonarchimedean (norm : K → ℝ) := 
λ x y, rank_one_valuation.norm_def_add_le x y

variables {K} [complete_space K] {L : Type*} [field L] [algebra K L] 

def disc_norm_extension (h_alg : algebra.is_algebraic K L) : mul_algebra_norm K L :=
spectral_mul_alg_norm h_alg (norm_is_nonarchimedean K)

def disc_normed_field_extension (h_alg : algebra.is_algebraic K L) : normed_field L :=
spectral_norm_to_normed_field h_alg (norm_is_nonarchimedean K)

def disc_normed_field_extension_uniform_space (h_alg : algebra.is_algebraic K L) : 
  uniform_space L :=
begin
  haveI : normed_field L := disc_normed_field_extension h_alg,
  apply_instance,
end

lemma disc_norm_extension_eq_root_zero_coeff (h_alg : algebra.is_algebraic K L) (x : L) :
  disc_norm_extension h_alg x = 
  ((rk1 K).hom (valued.v ((minpoly K x).coeff 0)))^(1/(minpoly K x).nat_degree : ℝ) :=
spectral_norm_eq_root_zero_coeff h_alg (norm_is_nonarchimedean K) x

lemma disc_norm_extension_eq_root_zero_coeff' (h_alg : algebra.is_algebraic K L) (x : L) :
  disc_norm_extension h_alg x = (with_zero_mult_int_to_nnreal (valuation_base_ne_zero K)
    (valued.v ((minpoly K x).coeff 0)))^(1/(minpoly K x).nat_degree : ℝ) :=
begin
  exact spectral_norm_eq_root_zero_coeff h_alg (norm_is_nonarchimedean K) x,
end

lemma pow_disc_norm_extension_eq_pow_root_zero_coeff' (h_alg : algebra.is_algebraic K L) (x : L)
  (n : ℕ) : 
  (disc_norm_extension h_alg x)^n = (with_zero_mult_int_to_nnreal (valuation_base_ne_zero K) 
    (valued.v ((minpoly K x).coeff 0)) ^ (n/(minpoly K x).nat_degree : ℝ)) :=
by  rw [div_eq_inv_mul, real.rpow_mul nnreal.zero_le_coe, disc_norm_extension_eq_root_zero_coeff',
    inv_eq_one_div, real.rpow_nat_cast]

lemma pow_disc_norm_extension_eq_pow_root_zero_coeff (h_alg : algebra.is_algebraic K L) (x : L)
  {n : ℕ} (hn : (minpoly K x).nat_degree ∣ n) : 
  (disc_norm_extension h_alg x)^n = (with_zero_mult_int_to_nnreal (valuation_base_ne_zero K) 
    (valued.v ((minpoly K x).coeff 0)) ^ (n/(minpoly K x).nat_degree)) :=
begin
  nth_rewrite 1 [← real.rpow_nat_cast],
  rw [nat.cast_div hn (nat.cast_ne_zero.mpr
    (ne_of_gt (minpoly.nat_degree_pos (is_algebraic_iff_is_integral.mp (h_alg x)))))],
  exact pow_disc_norm_extension_eq_pow_root_zero_coeff'  h_alg x n,
  { apply_instance }
end

lemma disc_norm_extension_nonneg (h_alg : algebra.is_algebraic K L) (x : L) :
  0 ≤ disc_norm_extension h_alg x :=
spectral_norm_nonneg _

lemma disc_norm_extension_is_nonarchimedean (h_alg : algebra.is_algebraic K L) :
  is_nonarchimedean (disc_norm_extension h_alg) :=
spectral_norm_is_nonarchimedean h_alg (norm_is_nonarchimedean K)

lemma disc_norm_extension_mul (h_alg : algebra.is_algebraic K L) (x y : L) :
  (disc_norm_extension h_alg (x * y)) = 
  (disc_norm_extension h_alg x) * (disc_norm_extension h_alg y) :=
spectral_norm_is_mul h_alg (norm_is_nonarchimedean K) x y

local attribute [-instance] disc_norm_field'

end is_discrete

variables {L : Type*} [field L] [algebra K L] 
include hv

lemma pow_valuation_unit_ne_zero [finite_dimensional K L] 
  (x : Lˣ) :
  (valued.v ((minpoly K x.1).coeff 0))^((finrank K L)/(minpoly K x.1).nat_degree) ≠ (0 : ℤₘ₀) :=
begin
  have h_alg : algebra.is_algebraic K L := algebra.is_algebraic_of_finite K L,
  have hdeg : 0 < finrank K L / (minpoly K x.val).nat_degree,
  { exact nat.div_pos (nat_degree_le (is_algebraic_iff_is_integral.mp (h_alg x.val)))
      (nat_degree_pos (is_algebraic_iff_is_integral.mp (h_alg x.val))), },
  rw [ne.def, pow_eq_zero_iff hdeg, valuation.zero_iff],
  exact coeff_zero_ne_zero (is_algebraic_iff_is_integral.mp (h_alg x.val)) (units.ne_zero x),
  apply_instance,
end

open polynomial

variables {K}

lemma valued_coeff_zero (x : K) :
  valued.v ((minpoly K ((algebra_map K L) x)).coeff 0) = valued.v x :=
by rw [minpoly.eq_X_sub_C, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, valuation.map_neg]

open function

variables [is_discrete hv.v]

lemma aux_pow_div [finite_dimensional K L] (x : Lˣ) : 
  (with_zero_mult_int_to_nnreal (valuation_base_ne_zero K)) 
    (valued.v ((minpoly K (x : L)).coeff 0) ^ (finrank K L / (minpoly K (x : L)).nat_degree)) =
  ((with_zero_mult_int_to_nnreal (valuation_base_ne_zero K)) 
    (valued.v ((minpoly K (x : L)).coeff 0)) ^ 
    (1 / ((minpoly K (x : L)).nat_degree : ℝ))) ^ (finrank K L : ℝ) :=
begin
  have h_alg : algebra.is_algebraic K L := algebra.is_algebraic_of_finite K L,
  rw [_root_.map_pow, ← nnreal.rpow_nat_cast,
   nat.cast_div (minpoly.degree_dvd (is_algebraic_iff_is_integral.mp (h_alg ↑x)))
    (nat.cast_ne_zero.mpr (ne_of_gt (minpoly.nat_degree_pos 
    (is_algebraic_iff_is_integral.mp (h_alg ↑x))))), div_eq_mul_inv, mul_comm (finrank K L : ℝ),
    nnreal.rpow_mul, ← one_div],
  apply_instance,
end

open nnreal 

variables [complete_space K] 

lemma map_mul_aux [finite_dimensional K L] (x y : Lˣ) : 
  valued.v ((minpoly K ((x : L) * ↑y)).coeff 0) ^ 
    (finrank K L / (minpoly K ((x : L) * ↑y)).nat_degree) = 
  valued.v ((minpoly K (x : L)).coeff 0) ^ (finrank K L / (minpoly K (x : L)).nat_degree) 
  * valued.v ((minpoly K (y : L)).coeff 0) ^ (finrank K L / (minpoly K (y : L)).nat_degree) :=
begin
  have h_alg : algebra.is_algebraic K L := algebra.is_algebraic_of_finite K L,
  have hinj : injective (with_zero_mult_int_to_nnreal (valuation_base_ne_zero K)),
  { exact (with_zero_mult_int_to_nnreal_strict_mono (one_lt_valuation_base K)).injective, },
  rw [← function.injective.eq_iff hinj, _root_.map_mul, ← units.coe_mul, aux_pow_div,
    aux_pow_div, aux_pow_div, ← mul_rpow,
    rpow_eq_rpow_iff (nat.cast_ne_zero.mpr (ne_of_gt finrank_pos))],
  ext,
  rw [nnreal.coe_mul, coe_rpow, coe_rpow, coe_rpow, ← disc_norm_extension_eq_root_zero_coeff' h_alg,
    ← disc_norm_extension_eq_root_zero_coeff' h_alg,
    ← disc_norm_extension_eq_root_zero_coeff' h_alg, units.coe_mul, _root_.map_mul],
  apply_instance,
  apply_instance,
end

variables (K L) 
def aux_hom [finite_dimensional K L] : 
  Lˣ →* (multiplicative ℤ) :=
{ to_fun   := λ x, with_zero.unzero (@pow_valuation_unit_ne_zero K _ _ _ _ _ _ x),
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

variables {K L}

lemma aux_hom_apply [finite_dimensional K L] (x : Lˣ) : 
  aux_hom K L x = with_zero.unzero (pow_valuation_unit_ne_zero K x) :=
rfl

open multiplicative

variables (K L)

def aux_d [finite_dimensional K L] : ℕ :=
int.nat_abs (int.subgroup_cyclic (subgroup.map (aux_hom K L) ⊤).to_add_subgroup).some

variables {K L} 
lemma aux_d_prop [finite_dimensional K L] : 
  subgroup.to_add_subgroup (subgroup.map (aux_hom K L) ⊤) =
    add_subgroup.closure {(aux_d K L : ℤ)} := 
by rw [(int.subgroup_cyclic (subgroup.map (aux_hom K L) ⊤).to_add_subgroup).some_spec,
    add_subgroup.closure_singleton_eq_zmultiples, add_subgroup.closure_singleton_eq_zmultiples,
    aux_d, int.zmultiples_nat_abs]

lemma aux_d_ne_zero [finite_dimensional K L] : aux_d K L ≠ 0 :=
begin
  have h_alg : algebra.is_algebraic K L := algebra.is_algebraic_of_finite K L,
  obtain ⟨x, hx⟩ := exists_uniformizer hv.v,
  have hx_unit : is_unit (x : K),
  { exact is_unit_iff_ne_zero.mpr (uniformizer_ne_zero hv.v hx) },
  set z : Lˣ := units.map (algebra_map K L).to_monoid_hom (is_unit.unit hx_unit) with hz,
  rw is_uniformizer at hx,
  by_contradiction h0,
  have h := aux_d_prop,
  rw [h0, zmod.nat_cast_self, add_subgroup.closure_singleton_zero, map_eq_bot_iff,
    subgroup.map_eq_bot_iff, top_le_iff] at h,
  have hz1 : aux_hom K L z = 1,
  { rw [← monoid_hom.mem_ker, h], exact subgroup.mem_top _ },
  have hzne1 : aux_hom K L z ≠ 1,
  { have hv : valued.v ((minpoly K ((units.map (algebra_map K L).to_monoid_hom) 
    hx_unit.unit).val).coeff 0) = valued.v (x : K),
    { rw [ring_hom.to_monoid_hom_eq_coe, units.val_eq_coe, units.coe_map, 
        is_unit.unit_spec, ring_hom.coe_monoid_hom, valued_coeff_zero] },
    rw [hz, aux_hom_apply, ne.def, ← with_zero.coe_inj, coe_unzero, hv, hx,
      ← of_add_neg_nat, ← of_add_zero, with_zero.coe_inj, ring_hom.to_monoid_hom_eq_coe, 
      units.val_eq_coe, units.coe_map, is_unit.unit_spec, ring_hom.coe_monoid_hom, int.coe_nat_div,
      of_add_neg, of_add_zero, inv_eq_one, of_add_eq_one, ← int.coe_nat_div, int.coe_nat_eq_zero,
      nat.div_eq_zero_iff (minpoly.nat_degree_pos (is_algebraic_iff_is_integral.mp (h_alg _)))],
    exact not_lt.mpr (minpoly.nat_degree_le (is_algebraic_iff_is_integral.mp (h_alg _))) },
  exact hzne1 hz1,
end

lemma aux_d_pos [finite_dimensional K L] : 0 < aux_d K L := nat.pos_of_ne_zero aux_d_ne_zero

-- This proof is ridiculous (TODO: golf)
lemma range_eq_aux_d_pow [finite_dimensional K L] :
  (subgroup.map (aux_hom K L) ⊤) = subgroup.closure {of_add (aux_d K L : ℤ)} :=
begin
  have h' : add_subgroup.to_subgroup (subgroup.to_add_subgroup (subgroup.map (aux_hom K L) ⊤)) =
    add_subgroup.to_subgroup (add_subgroup.closure {(aux_d K L : ℤ)}),
  { rw aux_d_prop, },
  convert h',
  { ext x,
    have hx : x ∈ subgroup.zpowers (of_add (aux_d K L : ℤ)) ↔ 
    x ∈ (subgroup.zpowers (of_add (aux_d K L : ℤ)) : set (multiplicative ℤ)),
    { refl },
    have hx' : x ∈ (add_subgroup.to_subgroup (add_subgroup.closure {(aux_d K L : ℤ)})) ↔
      x.to_add ∈ (add_subgroup.closure {(aux_d K L : ℤ)}),
    { simp only [add_subgroup.to_subgroup, rel_iso.coe_fn_mk, equiv.coe_fn_mk,
        add_submonoid.to_submonoid, add_subgroup.coe_to_add_submonoid],
      rw ← subgroup.mem_carrier,
      change x ∈ to_add ⁻¹' (↑(add_subgroup.closure {(aux_d K L : ℤ)}) : set ℤ)
      ↔ to_add x ∈ add_subgroup.closure {(aux_d K L : ℤ)},
      rw set.mem_preimage,
      refl,},
    have hx'' : x ∈ of_add '' (add_subgroup.zmultiples (aux_d K L : ℤ) : set ℤ) ↔
      x.to_add ∈ ↑(add_subgroup.zmultiples (aux_d K L : ℤ)),
    { simp only [set.mem_image, set_like.mem_coe],
      split,
      { rintros ⟨n, hn, hnx⟩, rw ← hnx, exact hn, },
      { intro h, exact ⟨to_add x, h, rfl⟩, }, },
    rw [subgroup.mem_closure_singleton, ← subgroup.mem_zpowers_iff, hx,
      ← of_add_image_zmultiples_eq_zpowers_of_add, hx', hx'', 
      add_subgroup.mem_closure_singleton, ← add_subgroup.mem_zmultiples_iff],
    refl, },
end

variable (K)

lemma aux_w [finite_dimensional K L] (x : Lˣ) : 
  ∃ (n : ℤ), (((of_add (-1 : ℤ))^n)^(aux_d K L) : ℤₘ₀) =
  (valued.v ((minpoly K (x : L)).coeff 0))^((finrank K L)/((minpoly K (x : L)).nat_degree)) :=
begin
  set y := (with_zero.unzero (pow_valuation_unit_ne_zero K x)),
  have h_mem : (with_zero.unzero (pow_valuation_unit_ne_zero K x)) ∈ 
    subgroup.closure ({of_add (aux_d K L : ℤ)} : set (multiplicative ℤ)),
  { rw [← range_eq_aux_d_pow, subgroup.mem_map],
    exact ⟨x, subgroup.mem_top x, rfl⟩ },
  rw subgroup.mem_closure_singleton at h_mem,
  obtain ⟨n, hn⟩ := h_mem,
  use - n,
  rw [with_zero.of_add_neg_one_pow_comm n, ← with_zero.coe_zpow, hn],
  exact with_zero.coe_unzero _,
end

def w_def [finite_dimensional K L] : L → ℤₘ₀ :=
λ x, by classical; exact if hx : x = 0 then 0 else 
  (of_add (-1 : ℤ))^(aux_w K  (is_unit_iff_ne_zero.mpr hx).unit).some

variable {K}

lemma w_def_apply [finite_dimensional K L]  (x : L) :
w_def K x = (if hx : x = 0 then 0 else 
  (of_add (-1 : ℤ))^(aux_w K (is_unit_iff_ne_zero.mpr hx).unit).some) := rfl

lemma w_def_mul [finite_dimensional K L] (x y : L) :
  w_def K (x * y) = w_def K x * w_def K y :=
begin
  have h_alg : algebra.is_algebraic K L := algebra.is_algebraic_of_finite K L,
  by_cases hx : x = 0,
  { have hxy : x * y = 0,
    { rw [hx, zero_mul] },
    rw [w_def_apply, dif_pos hxy, w_def_apply, dif_pos hx, zero_mul] },
    { by_cases hy : y = 0,
      { have hxy : x * y = 0,
        { rw [hy, mul_zero] },
        simp only [w_def_apply],
        rw [dif_pos hxy, dif_pos hy, mul_zero] },
      { have hxy : x * y ≠ 0,
        { exact mul_ne_zero hx hy, },
        simp only [w_def_apply],
        rw [dif_neg hx, dif_neg hy, dif_neg (mul_ne_zero hx hy)],
        have hinj : injective (with_zero_mult_int_to_nnreal (valuation_base_ne_zero K)),
        { exact (with_zero_mult_int_to_nnreal_strict_mono (one_lt_valuation_base K)).injective },
        rw [← function.injective.eq_iff hinj, ← pow_left_inj _ _ aux_d_pos, ← nnreal.coe_eq,
          _root_.map_mul, mul_pow, ← _root_.map_pow,
          (aux_w K (is_unit_iff_ne_zero.mpr hxy).unit).some_spec, nnreal.coe_mul],
        nth_rewrite 1 ← _root_.map_pow,
        rw (aux_w K (is_unit_iff_ne_zero.mpr hx).unit).some_spec,
        nth_rewrite 2 ← _root_.map_pow,
        rw [(aux_w K (is_unit_iff_ne_zero.mpr hy).unit).some_spec, _root_.map_pow,
          nnreal.coe_pow, ← pow_disc_norm_extension_eq_pow_root_zero_coeff h_alg,
          _root_.map_pow, nnreal.coe_pow, ← pow_disc_norm_extension_eq_pow_root_zero_coeff h_alg,
          _root_.map_pow, nnreal.coe_pow, ← pow_disc_norm_extension_eq_pow_root_zero_coeff h_alg,
         ← mul_pow, ← disc_norm_extension_mul h_alg],
        refl,
        repeat { exact minpoly.degree_dvd (is_algebraic_iff_is_integral.mp (h_alg _))},
        { exact zero_le' },
        { exact zero_le' }}},
end

variables (K L)

--set_option trace.class_instances true
def w [finite_dimensional K L] : valuation L ℤₘ₀ := 
{ to_fun    := w_def K,
  map_zero' := by rw [w_def_apply, dif_pos rfl],
  map_one'  := 
  begin
    rw [w_def_apply, dif_neg one_ne_zero],
    have h1 : (1 : L) ≠ 0 := one_ne_zero, 
    set u := (aux_w K (is_unit_iff_ne_zero.mpr h1).unit).some with hu_def,
    have hu : (↑(of_add (-1 : ℤ)) ^ u) ^ aux_d K L = 
      valued.v ((minpoly K ↑((is_unit_iff_ne_zero.mpr h1).unit)).coeff 0) ^ 
        (finrank K L / (minpoly K ((is_unit_iff_ne_zero.mpr h1).unit : L)).nat_degree) := 
    (aux_w K (is_unit_iff_ne_zero.mpr h1).unit).some_spec,
    simp only [is_unit.unit_spec, one, 
      coeff_sub, coeff_X_zero, coeff_one_zero, zero_sub, valuation.map_neg, valuation.map_one, 
      one_pow, inv_eq_one] at hu,
    simp only [← with_zero.coe_one, ← of_add_zero, ← with_zero.coe_zpow, 
      ← with_zero.coe_pow, with_zero.coe_inj, ← zpow_coe_nat, ← int.of_add_mul] at hu,
    have hu' := int.eq_zero_or_eq_zero_of_mul_eq_zero hu,
    rw or_eq_of_eq_false_right at hu',
    rw [← hu_def, ← with_zero.coe_one, ← of_add_zero, ← with_zero.coe_zpow, with_zero.coe_inj, 
      ← int.of_add_mul, hu'],
    { simp only [aux_d_ne_zero, nat.cast_eq_zero] },
    { exact ne_zero.one L },
  end,
  map_mul'  := w_def_mul,
  map_add_le_max' := λ x y,
  begin
    have h_alg : algebra.is_algebraic K L := algebra.is_algebraic_of_finite K L,
    by_cases hx : x = 0,
    { have hxy : x + y = y,
      { rw [hx, zero_add] },
      simp only [w_def_apply, dif_pos hx, hxy],
      rw max_eq_right, 
      exact le_refl _,
      { exact zero_le' }},
    { by_cases hy : y = 0,
      { have hxy : x + y = x,
        { rw [hy, add_zero] },
          simp only [w_def_apply, dif_pos hy, hxy],
          rw max_eq_left, 
          exact le_refl _,
        { exact zero_le' }},
      { by_cases hxy : x + y = 0,
        { simp only [w_def_apply, dif_pos hxy, zero_le'] },
        { simp only [w_def_apply, dif_neg hx, dif_neg hy, dif_neg hxy],
          set ux := (aux_w K (is_unit_iff_ne_zero.mpr hx).unit).some with hux_def,
          set uy := (aux_w K (is_unit_iff_ne_zero.mpr hy).unit).some with huy_def,
          set uxy := (aux_w K (is_unit_iff_ne_zero.mpr hxy).unit).some with huxy_def,
          rw [← hux_def, ← huy_def, ← huxy_def],
        rw _root_.le_max_iff,
        simp only [← with_zero.coe_zpow, coe_le_coe],
        have hd : 0 < (aux_d K L: ℤ), 
        { rw [int.coe_nat_pos],
          exact nat.pos_of_ne_zero aux_d_ne_zero, },
        rw [← zpow_le_zpow_iff' hd, zpow_coe_nat, zpow_coe_nat, ← coe_le_coe, 
          with_zero.coe_pow, with_zero.coe_zpow,
          (aux_w K (is_unit_iff_ne_zero.mpr hxy).unit).some_spec],
        rw [ with_zero.coe_pow, with_zero.coe_zpow,
          (aux_w K (is_unit_iff_ne_zero.mpr hx).unit).some_spec],
        rw [← zpow_le_zpow_iff' hd,zpow_coe_nat, zpow_coe_nat],
        nth_rewrite 1 [← coe_le_coe],
        simp only [with_zero.coe_pow, with_zero.coe_zpow,
          (aux_w K (is_unit_iff_ne_zero.mpr hxy).unit).some_spec,
          (aux_w K (is_unit_iff_ne_zero.mpr hy).unit).some_spec],
        simp only [← (with_zero_mult_int_to_nnreal_strict_mono 
          (one_lt_valuation_base K)).le_iff_le, ← nnreal.coe_le_coe],
        rw [_root_.map_pow, nnreal.coe_pow, ← real.rpow_nat_cast, nat.cast_div,
          ← pow_disc_norm_extension_eq_pow_root_zero_coeff' h_alg], --x + y
        rw [_root_.map_pow, nnreal.coe_pow, ← real.rpow_nat_cast _
          (finrank K L / (minpoly K _).nat_degree), nat.cast_div,
          ← pow_disc_norm_extension_eq_pow_root_zero_coeff' h_alg], -- x
        rw [_root_.map_pow, nnreal.coe_pow, ← real.rpow_nat_cast _
          (finrank K L / (minpoly K _).nat_degree), nat.cast_div,
          ← pow_disc_norm_extension_eq_pow_root_zero_coeff' h_alg], -- y
        have h_le : (disc_norm_extension h_alg) (x + y)  ≤ (disc_norm_extension h_alg) x ∨ 
          (disc_norm_extension h_alg) (x + y)  ≤ (disc_norm_extension h_alg) y,
        { rw ← _root_.le_max_iff,
          exact (disc_norm_extension_is_nonarchimedean h_alg) _ _ },
        cases h_le with hlex hley,
        { left,
          exact pow_le_pow_of_le_left (disc_norm_extension_nonneg h_alg _) hlex _ },
        { right,
          exact pow_le_pow_of_le_left (disc_norm_extension_nonneg h_alg _) hley _ },
        repeat { exact minpoly.degree_dvd (is_algebraic_iff_is_integral.mp (h_alg _))},
        repeat { rw nat.cast_ne_zero,
          exact ne_of_gt (minpoly.nat_degree_pos (is_algebraic_iff_is_integral.mp (h_alg _))) }}}}
  end }

variables {K L}

lemma w_apply [finite_dimensional K L] (x : L) : 
   w K L x = (if hx : x = 0 then 0 else 
    (of_add (-1 : ℤ))^(aux_w K (is_unit_iff_ne_zero.mpr hx).unit).some) :=
rfl

lemma w_apply_if_neg [finite_dimensional K L] {x : L} (hx : x ≠ 0) :
  w K L x = ((of_add (-1 : ℤ))^(aux_w K (is_unit_iff_ne_zero.mpr hx).unit).some) :=
by rw [w_apply, dif_neg hx]

variables (K L)

lemma exists_uniformizer [finite_dimensional K L] :
  ∃ (x : Lˣ), aux_hom K L x = of_add (-aux_d K L : ℤ) :=
begin
  have h_mem : of_add (aux_d K L : ℤ) ∈ subgroup.closure {of_add (aux_d K L : ℤ)},
  { exact subgroup.mem_closure_singleton.mpr ⟨1, by rw zpow_one⟩,},
  rw [← range_eq_aux_d_pow, subgroup.mem_map] at h_mem,
  obtain ⟨x, _, hx⟩ := h_mem,
  use x⁻¹,
  rw [map_inv, hx],
  refl,
end

instance is_discrete_of_finite [finite_dimensional K L]  :
  is_discrete (w K L) := 
begin
  set x := (exists_uniformizer K L).some,
  have hx := (exists_uniformizer K L).some_spec,
  rw ←  with_zero.coe_inj at hx,
  simp only [aux_hom, units.val_eq_coe, monoid_hom.coe_mk, coe_unzero, of_add_neg_nat] at hx,
  have hπ1 : w K L x = (multiplicative.of_add (-1 : ℤ)),
  { rw [w_apply_if_neg, ← with_zero.zpow_left_inj _ with_zero.coe_ne_zero 
      (nat.cast_ne_zero.mpr aux_d_ne_zero)],
    { have hx0 : (x : L) ≠ 0, { exact units.ne_zero _ },
      rw [zpow_coe_nat, zpow_coe_nat, ← hx],
      erw (aux_w K x).some_spec,
      refl, },
    { exact zpow_ne_zero _ with_zero.coe_ne_zero,
    exact units.ne_zero _ }},
  set π : (w K L).integer := ⟨(exists_uniformizer K L).some, 
    by rw [mem_integer, hπ1]; exact le_of_lt with_zero.of_add_neg_one_lt_one⟩, 
  have hπ : w K L (π : L) = (multiplicative.of_add (-1 : ℤ)) := hπ1,
  apply is_discrete_of_exists_uniformizer (w K L) hπ,
end

end extension

section complete

open valuation

variables {K : Type*} [field K] [hv : valued K ℤₘ₀] [is_discrete hv.v] 

include hv

-- Without finite_dimensional, the fails_quickly does not complain
variables {L : Type*} [field L] [algebra K L] [complete_space K] 

-- TODO: Maybe this can be an instance. Update: probably not (because of h_alg, plus the linter complains)
def uniform_space_extension (h_alg : algebra.is_algebraic K L) : 
  uniform_space L := 
disc_normed_field_extension_uniform_space h_alg

@[priority 100] instance extension_complete [finite_dimensional K L] : 
  @complete_space L (uniform_space_extension (algebra.is_algebraic_of_finite K L)) := 
begin
  letI : nontrivially_normed_field K := disc_norm_field' K,
  exact spectral_norm_complete_space (algebra.is_algebraic_of_finite K L) (norm_is_nonarchimedean K),
end

lemma extension_is_complete [finite_dimensional K L] : 
  @is_complete L (uniform_space_extension (algebra.is_algebraic_of_finite K L)) set.univ := 
begin
  rw ← complete_space_iff_is_complete_univ,
  apply_instance,
end

/- lemma integral_closure_eq_integer :
  (integral_closure hv.v.integer L).to_subring = (@valued.v L _ ℤₘ₀ _ _).integer :=
sorry -/
lemma integral_closure_eq_integer [finite_dimensional K L] :
  (integral_closure hv.v.integer L).to_subring = (w K L).integer :=
sorry

--Chapter 2, Section 2, Proposition 3 in Serre's Local Fields
lemma dvr_of_finite_extension : discrete_valuation_ring (integral_closure hv.v.integer L) := sorry
-- proof: make a local instance of valued on `L`

lemma integral_closure_finrank :
  finite_dimensional.finrank hv.v.integer (integral_closure hv.v.integer L) =
  finite_dimensional.finrank K L :=
sorry

variables [finite_dimensional K L] 

local notation `K₀` := hv.v.integer

local notation `L₀` := (w K L).integer

def integer.algebra : algebra K₀ L₀ :=
by rw ← integral_closure_eq_integer; exact (integral_closure ↥(valued.v.integer) L).algebra

end complete

section unramified

open discrete_valuation

variables {A : Type*} [comm_ring A] [is_domain A] [discrete_valuation_ring A]

lemma is_domain_of_irreducible {f : polynomial A} 
  (hf : irreducible (polynomial.map (algebra_map A (local_ring.residue_field A)) f)) :
  is_domain (adjoin_root f) :=
sorry

-- Ch. I, Section 6, Prop. 15 of Serre's "Local Fields"
lemma is_dvr_of_irreducible {f : polynomial A} 
  (hf : irreducible (polynomial.map (algebra_map A (local_ring.residue_field A)) f)) :
  @discrete_valuation_ring (adjoin_root f) _ (is_domain_of_irreducible hf) :=
sorry

-- Ch. I, Section 6, Cor. 1 of Serre's "Local Fields"
lemma is_dvr_of_irreducible' {f : polynomial A} 
  (hf : irreducible (polynomial.map (algebra_map A (local_ring.residue_field A)) f)) :
  is_integral_closure (adjoin_root f) A (fraction_ring (adjoin_root f)) :=
sorry

local notation `K` := fraction_ring A

variables (L : Type*) [field L] [algebra K L] [finite_dimensional K L] [algebra A L]
[is_scalar_tower A K L]

open finite_dimensional

--Serre's Proposition 16 in Chapter I, Section 6: we may want the algebra instance to become an\
-- explicit variable so that when we use the definition we do not need `@`.
noncomputable!
def minimal_poly_eq_residue_fields_of_unramified
  (hB : discrete_valuation_ring (integral_closure A L))
  [algebra (local_ring.residue_field A)
  (@local_ring.residue_field _ _ hB.to_local_ring)]
  (hpb : power_basis (local_ring.residue_field A)
  (@local_ring.residue_field _ _ hB.to_local_ring))
  (hdeg : finrank K L = hpb.dim) (x : (integral_closure A L))
  (hx : ideal.quotient.mk (@local_ring.maximal_ideal _ _ hB.to_local_ring) x = hpb.gen) : 
  (integral_closure A L) ≃+* algebra.adjoin A ({x} : set (integral_closure A L)) := sorry

noncomputable!
def minimal_poly_eq_residue_fields_of_unramified'
  (hB : discrete_valuation_ring (integral_closure A L))
  [algebra (local_ring.residue_field A)
  (@local_ring.residue_field _ _ hB.to_local_ring)]
  (hpb : power_basis (local_ring.residue_field A)
  (@local_ring.residue_field _ _ hB.to_local_ring))
  (hdeg : finrank K L = hpb.dim) (x : (integral_closure A L))
  (hx : ideal.quotient.mk (@local_ring.maximal_ideal _ _ hB.to_local_ring) x = hpb.gen) : 
  (integral_closure A L) ≃+* adjoin_root (minpoly A x) := sorry


-- We need to indicate in the doctring that h_alg is not an instance so when we apply it 
-- with local fields...
variables {B : Type*} [comm_ring B] [is_domain B] [discrete_valuation_ring B] (h_alg : algebra A B)

local notation `e(` B`,`A`)` := ideal.ramification_idx h_alg.to_ring_hom
  (local_ring.maximal_ideal A) (local_ring.maximal_ideal B)

lemma uniformizer_iff_unramified {a : A} (ha : is_uniformizer valued.v (↑a : fraction_ring A)) :
  is_uniformizer valued.v (↑(h_alg.to_ring_hom a) : fraction_ring B) ↔ e(B,A) = 1 :=
sorry

end unramified
