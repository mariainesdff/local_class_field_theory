import number_theory.ramification_inertia
import discrete_valuation_ring.basic
import from_mathlib.normed_valued
import for_mathlib.rank_one_valuation
import spectral_norm
import with_zero

noncomputable theory

open multiplicative with_zero
open_locale discrete_valuation nnreal

namespace add_subgroup

lemma closure_singleton_eq_zmultiples {A : Type*} [add_group A] (a : A) :
  closure {a} = zmultiples a :=
by ext n; rw [mem_closure_singleton, mem_zmultiples_iff]

end add_subgroup

namespace minpoly

theorem degree_dvd {K : Type*} [field K] {L : Type*} [field L] [algebra K L] {x : L}
  [finite_dimensional K L] (hx : is_integral K x) :
  (minpoly K x).nat_degree ∣ (finite_dimensional.finrank K L) :=
sorry

end minpoly

section is_rank_one

variables {K : Type*} [field K] 

def is_rank_one_of_is_discrete (v : valuation K ℤₘ₀) [is_discrete v]
  {e : ℝ≥0} (he0 : e ≠ 0) (he1 : 1 < e) : is_rank_one v :=
{ hom         := with_zero_mult_int_to_nnreal he0,
  strict_mono := with_zero_mult_int_to_nnreal_strict_mono he1,
  nontrivial  := 
  begin
    obtain ⟨π, hπ⟩ := discrete_valuation.exists_uniformizer v,
    exact ⟨π, ne_of_gt (discrete_valuation.uniformizer_valuation_pos v hπ),
      ne_of_lt (discrete_valuation.uniformizer_valuation_lt_one v hπ)⟩,
  end }

end is_rank_one

namespace discrete_valuation

def valuation_base (K : Type*) [field K] [hv : valued K ℤₘ₀] [is_discrete hv.v] : ℝ≥0 :=
if 1 < nat.card (local_ring.residue_field hv.v.integer)
  then nat.card (local_ring.residue_field hv.v.integer)
  else 2

lemma one_lt_valuation_base (K : Type*) [field K] [hv : valued K ℤₘ₀] [is_discrete hv.v] : 
  1 < valuation_base K :=
begin
  rw valuation_base,
  split_ifs with hlt hge,
  { rw [nat.one_lt_cast], exact hlt },
  { exact one_lt_two }
end

lemma valuation_base_ne_zero (K : Type*) [field K] [hv : valued K ℤₘ₀] [is_discrete hv.v]  : 
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
    obtain ⟨x, hx⟩ := discrete_valuation.exists_uniformizer hv.v,
    use x.1⁻¹,
    erw [@norm_inv K (@normed_field.to_normed_division_ring K (disc_norm_field K)),
      one_lt_inv_iff, rank_one_valuation.norm_lt_one_iff_val_lt_one,
      rank_one_valuation.norm_pos_iff_val_pos],
    exact ⟨discrete_valuation.uniformizer_valuation_pos hv.v hx,
     discrete_valuation.uniformizer_valuation_lt_one hv.v hx⟩,
  end
  ..(@rank_one_valuation.valued_field.to_normed_field K _ ℤₘ₀ _ _ (rk1 K))  } 

local attribute [priority 100, instance] disc_norm_field'

lemma norm_is_nonarchimedean : is_nonarchimedean (norm : K → ℝ) := 
λ x y, rank_one_valuation.norm_def_add_le x y

-- TODO: deduce h_alg from [finite_dimensional K L]

variables {K} [complete_space K] {L : Type*} [field L] [algebra K L] 

def disc_norm_extension (h_alg : algebra.is_algebraic K L) : mul_algebra_norm K L :=
spectral_mul_alg_norm h_alg (norm_is_nonarchimedean K)

def disc_normed_field_extension (h_alg : algebra.is_algebraic K L) : normed_field L :=
spectral_norm_to_normed_field h_alg (norm_is_nonarchimedean K)

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

local attribute [-instance] disc_norm_field'

end is_discrete

variables {K} {L : Type*} [field L] [algebra K L] 
include hv

lemma pow_valuation_unit_ne_zero [finite_dimensional K L] (h_alg : algebra.is_algebraic K L) 
  (x : Lˣ) :
  (valued.v ((minpoly K x.1).coeff 0))^((finrank K L)/(minpoly K x.1).nat_degree) ≠ (0 : ℤₘ₀) :=
begin
  have hdeg : 0 < finrank K L / (minpoly K x.val).nat_degree,
  { exact nat.div_pos (nat_degree_le (is_algebraic_iff_is_integral.mp (h_alg x.val)))
      (nat_degree_pos (is_algebraic_iff_is_integral.mp (h_alg x.val))), },
  rw [ne.def, pow_eq_zero_iff hdeg, valuation.zero_iff],
  exact coeff_zero_ne_zero (is_algebraic_iff_is_integral.mp (h_alg x.val)) (units.ne_zero x),
  apply_instance,
end

open polynomial

lemma valued_coeff_zero (x : K) :
  valued.v ((minpoly K ((algebra_map K L) x)).coeff 0) = valued.v x :=
by rw [minpoly.eq_X_sub_C, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, valuation.map_neg]

open function

variables [is_discrete hv.v]

lemma aux_pow_div [finite_dimensional K L] (h_alg : algebra.is_algebraic K L) (x : Lˣ) : 
  (with_zero_mult_int_to_nnreal (valuation_base_ne_zero K)) 
    (valued.v ((minpoly K (x : L)).coeff 0) ^ (finrank K L / (minpoly K (x : L)).nat_degree)) =
  ((with_zero_mult_int_to_nnreal (valuation_base_ne_zero K)) 
    (valued.v ((minpoly K (x : L)).coeff 0)) ^ 
    (1 / ((minpoly K (x : L)).nat_degree : ℝ))) ^ (finrank K L : ℝ) :=
begin
  rw [map_pow, ← nnreal.rpow_nat_cast,
   nat.cast_div (minpoly.degree_dvd (is_algebraic_iff_is_integral.mp (h_alg ↑x)))
    (nat.cast_ne_zero.mpr (ne_of_gt (minpoly.nat_degree_pos 
    (is_algebraic_iff_is_integral.mp (h_alg ↑x))))), div_eq_mul_inv, mul_comm (finrank K L : ℝ),
    nnreal.rpow_mul, ← one_div],
  apply_instance,
end

open nnreal 

variables [complete_space K] 

lemma map_mul_aux [finite_dimensional K L] (h_alg : algebra.is_algebraic K L) (x y : Lˣ) : 
  valued.v ((minpoly K ((x : L) * ↑y)).coeff 0) ^ 
    (finrank K L / (minpoly K ((x : L) * ↑y)).nat_degree) = 
  valued.v ((minpoly K (x : L)).coeff 0) ^ (finrank K L / (minpoly K (x : L)).nat_degree) 
  * valued.v ((minpoly K (y : L)).coeff 0) ^ (finrank K L / (minpoly K (y : L)).nat_degree) :=
begin
  have hinj : injective (with_zero_mult_int_to_nnreal (valuation_base_ne_zero K)),
  { exact (with_zero_mult_int_to_nnreal_strict_mono (one_lt_valuation_base K)).injective, },
  have hna := norm_is_nonarchimedean K,
  rw [← function.injective.eq_iff hinj, map_mul, ← units.coe_mul, aux_pow_div h_alg,
    aux_pow_div h_alg, aux_pow_div h_alg, ← mul_rpow,
    rpow_eq_rpow_iff (nat.cast_ne_zero.mpr (ne_of_gt finrank_pos))],
  ext,
  rw [nnreal.coe_mul, coe_rpow, coe_rpow, coe_rpow, ← disc_norm_extension_eq_root_zero_coeff' h_alg,
    ← disc_norm_extension_eq_root_zero_coeff' h_alg,
    ← disc_norm_extension_eq_root_zero_coeff' h_alg, units.coe_mul, map_mul],
  apply_instance,
  apply_instance,
end

def aux_hom [finite_dimensional K L] (h_alg : algebra.is_algebraic K L) : 
  Lˣ →* (multiplicative ℤ) :=
{ to_fun   := λ x, with_zero.unzero (pow_valuation_unit_ne_zero h_alg x),
  map_one' := by simp only [units.val_eq_coe, units.coe_one, one, polynomial.coeff_sub, 
    polynomial.coeff_X_zero, polynomial.coeff_one_zero, zero_sub, valuation.map_neg, 
    valuation.map_one, one_pow, unzero_coe],
  map_mul' := λ x y,
  begin
    simp only [units.val_eq_coe, units.coe_mul],
    rw [← with_zero.coe_inj, with_zero.coe_mul, with_zero.coe_unzero, with_zero.coe_unzero, 
      with_zero.coe_unzero],
    exact map_mul_aux h_alg x y,
  end } 

lemma aux_hom_apply [finite_dimensional K L] (h_alg : algebra.is_algebraic K L) (x : Lˣ) : 
  aux_hom h_alg x = with_zero.unzero (pow_valuation_unit_ne_zero h_alg x) :=
rfl

open multiplicative

def aux_d [finite_dimensional K L] (h_alg : algebra.is_algebraic K L) : ℕ :=
int.nat_abs (int.subgroup_cyclic (subgroup.map (aux_hom h_alg) ⊤).to_add_subgroup).some

lemma aux_d_prop [finite_dimensional K L] (h_alg : algebra.is_algebraic K L) : 
  subgroup.to_add_subgroup (subgroup.map (aux_hom h_alg) ⊤) =
    add_subgroup.closure {(aux_d h_alg : ℤ)} := 
begin
  rw [(int.subgroup_cyclic (subgroup.map (aux_hom h_alg) ⊤).to_add_subgroup).some_spec,
    add_subgroup.closure_singleton_eq_zmultiples, add_subgroup.closure_singleton_eq_zmultiples,
    aux_d, int.zmultiples_nat_abs],
end


lemma aux_d_ne_zero [finite_dimensional K L] (h_alg : algebra.is_algebraic K L) :
  aux_d h_alg ≠ 0 :=
begin
  obtain ⟨x, hx⟩ := discrete_valuation.exists_uniformizer hv.v,
  have hx_unit : is_unit (x : K),
  { rw [is_unit_iff_ne_zero, ne.def, subring.coe_eq_zero_iff],
    exact discrete_valuation.uniformizer_ne_zero hv.v hx },
  set z : Lˣ := units.map (algebra_map K L).to_monoid_hom (is_unit.unit hx_unit) with hz,
  rw discrete_valuation.is_uniformizer at hx,
  by_contradiction h0,
  have h := aux_d_prop h_alg,
  rw [h0, zmod.nat_cast_self, add_subgroup.closure_singleton_zero, map_eq_bot_iff,
    subgroup.map_eq_bot_iff, top_le_iff] at h,
  have hz1 : aux_hom h_alg z = 1,
  { rw [← monoid_hom.mem_ker, h], exact subgroup.mem_top _ },
  have hzne1 : aux_hom h_alg z ≠ 1,
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


-- This proof is ridiculous (TODO: golf)
lemma range_eq_aux_d_pow [finite_dimensional K L] (h_alg : algebra.is_algebraic K L) :
  (subgroup.map (aux_hom h_alg) ⊤) = subgroup.closure {of_add (aux_d h_alg : ℤ)} :=
begin
  have h' : add_subgroup.to_subgroup (subgroup.to_add_subgroup (subgroup.map (aux_hom h_alg) ⊤)) =
    add_subgroup.to_subgroup (add_subgroup.closure {(aux_d h_alg : ℤ)}),
  { rw aux_d_prop, },
  convert h',
  { ext x,
    have hx : x ∈ subgroup.zpowers (of_add (aux_d h_alg : ℤ)) ↔ 
    x ∈ (subgroup.zpowers (of_add (aux_d h_alg : ℤ)) : set (multiplicative ℤ)),
    { refl },
    have hx' : x ∈ (add_subgroup.to_subgroup (add_subgroup.closure {(aux_d h_alg : ℤ)})) ↔
      x.to_add ∈ (add_subgroup.closure {(aux_d h_alg : ℤ)}),
    { simp only [add_subgroup.to_subgroup, rel_iso.coe_fn_mk, equiv.coe_fn_mk,
        add_submonoid.to_submonoid, add_subgroup.coe_to_add_submonoid],
      rw ← subgroup.mem_carrier,
      change x ∈ to_add ⁻¹' (↑(add_subgroup.closure {(aux_d h_alg : ℤ)}) : set ℤ)
      ↔ to_add x ∈ add_subgroup.closure {(aux_d h_alg : ℤ)},
      rw set.mem_preimage,
      refl,},
    have hx'' : x ∈ of_add '' (add_subgroup.zmultiples (aux_d h_alg : ℤ) : set ℤ) ↔
      x.to_add ∈ ↑(add_subgroup.zmultiples (aux_d h_alg : ℤ)),
    { simp only [set.mem_image, set_like.mem_coe],
      split,
      { rintros ⟨n, hn, hnx⟩, rw ← hnx, exact hn, },
      { intro h, exact ⟨to_add x, h, rfl⟩, }, },
    rw [subgroup.mem_closure_singleton, ← subgroup.mem_zpowers_iff, hx,
      ← of_add_image_zmultiples_eq_zpowers_of_add, hx', hx'', 
      add_subgroup.mem_closure_singleton, ← add_subgroup.mem_zmultiples_iff],
    refl, },
end

lemma aux_d_divides [finite_dimensional K L] (h_alg : algebra.is_algebraic K L) (x : L) : 
  (aux_d h_alg) ∣ ((finrank K L)/(minpoly K x).nat_degree) :=
begin
  rw nat.dvd_div_iff,
  sorry,
  { sorry }
end

--set_option trace.class_instances true
def w [finite_dimensional K L] (h_alg : algebra.is_algebraic K L) :
  valuation L ℤₘ₀ := 
{ to_fun    := λ x, by classical; exact if x = 0 then 0 else 
    (valued.v ((minpoly K x).coeff 0))^((finrank K L)/((aux_d h_alg)*(minpoly K x).nat_degree)),
  map_zero' := by rw if_pos rfl,
  map_one'  := 
  begin
    rw [if_neg one_ne_zero, minpoly.one, polynomial.coeff_sub, polynomial.coeff_X_zero, 
      polynomial.coeff_one_zero, zero_sub, valuation.map_neg, valuation.map_one, one_pow],
    apply_instance,
  end,
  map_mul'  := λ x y,
  begin
    by_cases hx : x = 0,
    { have hxy : x * y = 0,
      { rw [hx, zero_mul] },
      rw [if_pos hx, if_pos hxy, zero_mul] },
    { by_cases hy : y = 0,
      { have hxy : x * y = 0,
      { rw [hy, mul_zero] },
        rw [if_pos hy, if_pos hxy, mul_zero]  },
      { have hxy : x * y ≠ 0,
        { sorry },
        rw [if_neg hx, if_neg hy, if_neg hxy],
        sorry } },
  end,
  map_add_le_max' := sorry }

lemma w_apply [finite_dimensional K L] (h_alg : algebra.is_algebraic K L)
  (x : L):  w h_alg x = (if x = 0 then 0 else 
    (valued.v ((minpoly K x).coeff 0))^((finrank K L)/((aux_d h_alg)*(minpoly K x).nat_degree))) :=
rfl

lemma w_apply_if_neg [finite_dimensional K L] (h_alg : algebra.is_algebraic K L)
  {x : L} (hx : x ≠ 0) :  w h_alg x = 
  (valued.v ((minpoly K x).coeff 0))^((finrank K L)/((aux_d h_alg)*(minpoly K x).nat_degree)) :=
by rw [w_apply, if_neg hx]


lemma exists_uniformizer [finite_dimensional K L] 
  (h_alg : algebra.is_algebraic K L) :
  ∃ (x : Lˣ), aux_hom h_alg x = of_add (-aux_d h_alg : ℤ) :=
begin
  have h_subgp := range_eq_aux_d_pow h_alg,
  have h_mem : of_add (aux_d h_alg : ℤ) ∈ subgroup.closure {of_add (aux_d h_alg : ℤ)},
  { exact subgroup.mem_closure_singleton.mpr ⟨1, by rw zpow_one⟩,},
  rw [← range_eq_aux_d_pow h_alg, subgroup.mem_map] at h_mem,
  obtain ⟨x, _, hx⟩ := h_mem,
  use x⁻¹,
  rw [map_inv, hx],
  refl,
end

lemma foo [finite_dimensional K L] (h_alg : algebra.is_algebraic K L) : 
  (of_add (aux_d h_alg : ℤ) : ℤₘ₀) = (of_add (1 : ℤ))^(aux_d h_alg) :=
begin
  rw ← with_zero.coe_pow,
  rw with_zero.coe_inj,
  rw ← one_mul (aux_d h_alg : ℤ), 
  rw int.of_add_mul,
  rw [zpow_coe_nat],
end

instance hw [decidable_eq L] [finite_dimensional K L] (h_alg : algebra.is_algebraic K L) :
  is_discrete (w h_alg) := 
begin
  set x := (exists_uniformizer h_alg).some with hx_def,
  have hx := (exists_uniformizer h_alg).some_spec,
  rw ←  with_zero.coe_inj at hx,
  simp only [aux_hom] at hx,
  simp only [units.val_eq_coe, monoid_hom.coe_mk, coe_unzero] at hx,
  rw of_add_neg_nat at hx,
  have hπ1 : w h_alg ((exists_uniformizer h_alg).some) = (multiplicative.of_add (-1 : ℤ)),
  { rw w_apply_if_neg,
    rw ← with_zero.zpow_left_inj _ with_zero.coe_ne_zero (nat.cast_ne_zero.mpr (aux_d_ne_zero h_alg)),
    { conv_rhs{rw zpow_coe_nat},
      rw ← hx,
      simp only [of_add_neg, zpow_coe_nat],

      rw ← pow_mul,
      rw mul_comm _ (aux_d h_alg),
      sorry },
    { apply pow_ne_zero,
      simp only [of_add_neg, ne.def, valuation.zero_iff],
      sorry},
    { exact units.ne_zero _ }},
  set π : (w h_alg).integer := ⟨(exists_uniformizer h_alg).some, 
    by rw [valuation.mem_integer, hπ1]; exact le_of_lt with_zero.of_add_neg_one_le_one⟩, 
  have hπ : w h_alg (π : L) = (multiplicative.of_add (-1 : ℤ)) := hπ1,
  apply discrete_valuation.is_discrete_of_exists_uniformizer (w h_alg) hπ,
end

end extension

section complete

open valuation

variables (K : Type*) [field K] [hv : valued K ℤₘ₀] [is_discrete hv.v] 

include hv

-- Without finite_dimensional, the fails_quickly does not complain
variables (L : Type*) [field L] [algebra K L] [complete_space K] 

-- TODO: Maybe this can be an instance
def uniform_space_extension : uniform_space L := sorry

lemma extension_is_complete [finite_dimensional K L] : @is_complete L (uniform_space_extension K L) set.univ := sorry

--instance is_discrete_of_finite : is_discrete (@valued.v L _ ℤₘ₀ _ _) := sorry
instance is_discrete_of_finite [finite_dimensional K L] (h_alg : algebra.is_algebraic K L) : 
  is_discrete (w h_alg) := sorry

/- lemma integral_closure_eq_integer :
  (integral_closure hv.v.integer L).to_subring = (@valued.v L _ ℤₘ₀ _ _).integer :=
sorry -/
lemma integral_closure_eq_integer [finite_dimensional K L] (h_alg : algebra.is_algebraic K L) :
  (integral_closure hv.v.integer L).to_subring = (w h_alg).integer :=
sorry

--Chapter 2, Section 2, Proposition 3 in Serre's Local Fields
lemma dvr_of_finite_extension : discrete_valuation_ring (integral_closure hv.v.integer L) := sorry
-- proof: make a local instance of valued on `L`

lemma integral_closure_finrank :
  finite_dimensional.finrank hv.v.integer (integral_closure hv.v.integer L) =
  finite_dimensional.finrank K L :=
sorry

variables [finite_dimensional K L]  (h_alg : algebra.is_algebraic K L) 

local notation `K₀` := hv.v.integer

local notation `L₀` := (w h_alg).integer

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


-- We need to indicate in the doctring that h_alg is not an instance so when we apply it with local fields...
variables {B : Type*} [comm_ring B] [is_domain B] [discrete_valuation_ring B] (h_alg : algebra A B)

local notation `e(` B`,`A`)` := ideal.ramification_idx h_alg.to_ring_hom
  (local_ring.maximal_ideal A) (local_ring.maximal_ideal B)

lemma uniformizer_iff_unramified {a : A} (ha : is_uniformizer valued.v (↑a : fraction_ring A)) :
  is_uniformizer valued.v (↑(h_alg.to_ring_hom a) : fraction_ring B) ↔ e(B,A) = 1 :=
sorry

end unramified
