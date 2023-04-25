import discrete_valuation_ring.basic
import from_mathlib.normed_valued
import spectral_norm

noncomputable theory

open_locale discrete_valuation nnreal

def with_zero_mult_int_to_nnreal_def (e : nnreal)  : ℤₘ₀ → ℝ≥0 := 
λ x, if hx : x = 0 then 0 else e^(multiplicative.to_add (with_zero.unzero hx))

open with_zero

def with_zero_mult_int_to_nnreal {e : nnreal} (he : e ≠ 0)  : ℤₘ₀ →*₀ ℝ≥0 := 
{ to_fun    := with_zero_mult_int_to_nnreal_def e,
  map_zero' := by { simp only [with_zero_mult_int_to_nnreal_def], rw dif_pos, refl },
  map_one'  := begin
    simp only [with_zero_mult_int_to_nnreal_def], rw dif_neg,
    { simp only [unzero_coe, to_add_one, zpow_zero] },
    { exact ne_zero.ne 1 },
  end,
  map_mul'  := λ x y, begin
    simp only [with_zero_mult_int_to_nnreal_def],
    by_cases hxy : x * y = 0,
    { cases (zero_eq_mul.mp (eq.symm hxy)) with hx hy, --either x = 0 or y = 0
      { rw [dif_pos hxy, dif_pos hx, zero_mul] },
      { rw [dif_pos hxy, dif_pos hy, mul_zero] },},
    { cases (mul_ne_zero_iff.mp hxy) with hx hy, --  x ≠ 0 and y ≠ 0
      rw [dif_neg hxy, dif_neg hx, dif_neg hy, ← zpow_add' (or.inl he)], 
      apply congr_arg,
      rw ← to_add_mul,
      apply congr_arg,
      rw [← with_zero.coe_inj, with_zero.coe_mul, coe_unzero hx,coe_unzero hy, coe_unzero hxy] },
  end }

lemma with_zero_mult_int_to_nnreal_strict_mono {e : nnreal} (he : 1 < e) : 
  strict_mono (with_zero_mult_int_to_nnreal (ne_zero_of_lt he))  := 
begin
  intros x y hxy,
  simp only [with_zero_mult_int_to_nnreal, with_zero_mult_int_to_nnreal_def, 
    monoid_with_zero_hom.coe_mk],
  split_ifs with hx hy hy,
  { simp only [hy, not_lt_zero'] at hxy, exfalso, exact hxy },
  { apply nnreal.zpow_pos (ne_zero_of_lt he) },
  { simp only [hy, not_lt_zero'] at hxy, exfalso, exact hxy },
  { rw [zpow_lt_iff_lt he, multiplicative.to_add_lt, ← with_zero.coe_lt_coe,
      with_zero.coe_unzero hx, with_zero.coe_unzero hy],
    exact hxy }
end 

section is_rank_one

variables {K : Type*} [field K] 

def is_rank_one_of_is_discrete (v : valuation K ℤₘ₀) [is_discrete v]
  {e : ℝ≥0} (he0 : e ≠ 0) (he1 : 1 < e) : is_rank_one v :=
{ hom         := with_zero_mult_int_to_nnreal he0,
  strict_mono := with_zero_mult_int_to_nnreal_strict_mono he1,
  nontrivial  := 
  begin
    obtain ⟨π, hπ⟩ := discrete_valuation.exists_uniformizer v,
    use π,
    split,
    { sorry },
    { sorry }
  end }

end is_rank_one

section


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

end

variables (K : Type*) [field K] [hv : valued K ℤₘ₀] [is_discrete hv.v]

instance rk1 : is_rank_one hv.v := is_rank_one_of_is_discrete hv.v (valuation_base_ne_zero K)
  (one_lt_valuation_base K)
  
include hv

@[priority 100] instance disc_norm_field : normed_field K :=
rank_one_valuation.valued_field.to_normed_field K ℤₘ₀
--@rank_one_valuation.valued_field.to_normed_field K _ ℤₘ₀ _ _ (rk1 K)

/- @[priority 100] instance disc_norm_field' : nontrivially_normed_field K :=
{ non_trivial := sorry,
  ..(@rank_one_valuation.valued_field.to_normed_field K _ ℤₘ₀ _ _ (rk1 K)) } -/

/- noncomputable! def aux_hom' {W : Type*} [field W] : 
  Wˣ →ₙ* (multiplicative ℤ) := sorry -/

#exit

lemma norm_is_nonarchimedean : is_nonarchimedean (norm : K → ℝ) := sorry

variables {K} [complete_space K] {L : Type*} [field L] [algebra K L] 

def disc_norm_extension (h_alg : algebra.is_algebraic K L) : mul_algebra_norm K L :=
spectral_mul_alg_norm h_alg (norm_is_nonarchimedean K)

def disc_normed_field_extension (h_alg : algebra.is_algebraic K L) : normed_field L :=
spectral_norm_to_normed_field h_alg (norm_is_nonarchimedean K)

lemma disc_norm_extension_eq_root_zero_coeff (h_alg : algebra.is_algebraic K L) 
 (hna : is_nonarchimedean (norm : K → ℝ)) (x : L) :
  disc_norm_extension h_alg x = ((rk1 K).hom (valued.v ((minpoly K x).coeff 0)))^(1/(minpoly K x).nat_degree : ℝ) :=
spectral_norm_eq_root_zero_coeff h_alg (norm_is_nonarchimedean K) x

lemma disc_norm_extension_eq_root_zero_coeff' (h_alg : algebra.is_algebraic K L) 
 (hna : is_nonarchimedean (norm : K → ℝ)) (x : L) :
  disc_norm_extension h_alg x = (with_zero_mult_int_to_nnreal (valuation_base_ne_zero K)
    (valued.v ((minpoly K x).coeff 0)))^(1/(minpoly K x).nat_degree : ℝ) :=
begin
  exact spectral_norm_eq_root_zero_coeff h_alg (norm_is_nonarchimedean K) x,
end

--  e^(multiplicative.to_add (with_zero.unzero hx))

open finite_dimensional

variables (K L)
noncomputable! def aux_hom /- (h_alg : algebra.is_algebraic K L) 
  (hna : is_nonarchimedean (norm : K → ℝ)) -/ : 
  Lˣ →* (multiplicative ℤ) :=
{ to_fun := λ x, --TODO : convert to term mode (extract proof to lemma)
  begin
    have hx : (valued.v ((minpoly K x.1).coeff 0))^((finrank K L)/(minpoly K x.1).nat_degree) ≠
      (0 : ℤₘ₀),
    { sorry },
    apply with_zero.unzero hx,
  end,
  map_one' := sorry,
  map_mul' := sorry } 

--variables (h_alg : algebra.is_algebraic K L) (hna : is_nonarchimedean (norm : K → ℝ))
def aux_d : ℕ :=
subgroup.index (subgroup.map (aux_hom K L) ⊤)

lemma aux_d_divides 
  (x : L) : (aux_d K L) ∣ ((finrank K L)/(minpoly K x).nat_degree) :=
sorry

--variables (h_alg : algebra.is_algebraic K L) (x : L)

--#check disc_norm_extension K L h_alg x

def w [decidable_eq L] : valuation L ℤₘ₀ := 
{ to_fun    := λ x, if x = 0 then 0 else 
    (valued.v ((minpoly K x).coeff 0))^((finrank K L)/((aux_d K L)*(minpoly K x).nat_degree)),
  map_zero' := by rw if_pos rfl,
  map_one'  := 
  begin
    
    sorry,
  end,
  map_mul'  := sorry,
  map_add_le_max' := sorry }

instance hw [decidable_eq L] : is_discrete (w K L) := sorry



