import complete_dvr

variables {A : Type*} [comm_ring A] 

open_locale discrete_valuation

/- We insist that `v` takes values in ℤₘ₀ in order to define uniformizers as the elements in `K`
whose valuation is exactly `with_zero.multiplicative (- 1) : ℤₘ₀`-/
class is_discrete (v : valuation A ℤₘ₀) :=
(surj : function.surjective v)

open valuation ideal is_dedekind_domain multiplicative with_zero

namespace discrete_valuation

variables [is_domain A] [discrete_valuation_ring A]

instance : valued (fraction_ring A) ℤₘ₀ := sorry

instance : is_discrete (@valued.v (fraction_ring A) _ ℤₘ₀ _ _) := sorry

variables {R : Type*} [comm_ring R] (vR : valuation R ℤₘ₀)

def is_uniformizer (π : R) : Prop := 
vR π = (multiplicative.of_add (- 1 : ℤ) : ℤₘ₀)

variables {K : Type*} [field K] (v : valuation K ℤₘ₀) 

local notation `K₀` := v.integer

@[ext] structure uniformizer :=
(val : v.integer)
(valuation_eq_neg_one : v val = (multiplicative.of_add (- 1 : ℤ) : ℤₘ₀))

def is_discrete_of_exists_uniformizer {π : K₀} (hπ : is_uniformizer v (π : K)) : 
  is_discrete v :=
⟨begin
  intro x,
  apply with_zero.cases_on x,
  { exact ⟨0, valuation.map_zero v⟩ },
  { rw is_uniformizer at hπ,
    intro m,
    use π^(- multiplicative.to_add m),
    rw [map_zpow₀, hπ, ← coe_zpow, coe_inj, ← of_add_zsmul, ← zsmul_neg', neg_neg, zsmul_one,
      int.cast_id, of_add_to_add] }
end⟩

lemma uniformizer_ne_zero {π : K₀} (hπ : is_uniformizer v (π : K)) : π ≠ 0 := 
begin
  intro h0,
  rw [h0, is_uniformizer, algebra_map.coe_zero, valuation.map_zero] at hπ,
  exact with_zero.zero_ne_coe hπ,
end

lemma uniformizer_ne_zero' (π : uniformizer v) : π.1 ≠ 0 := 
uniformizer_ne_zero v π.2

lemma uniformizer_valuation_pos {π : K₀} (hπ : is_uniformizer v (π : K)) : 0 < v (π : K) := 
begin
  rw [zero_lt_iff, ne.def, zero_iff, subring.coe_eq_zero_iff],
  exact uniformizer_ne_zero v hπ,
end

lemma uniformizer_not_is_unit {π : K₀} (hπ : is_uniformizer v (π : K)) : ¬ is_unit π := 
begin
  intro h,
  have h1 := @valuation.integers.one_of_is_unit K ℤₘ₀ _ _ v v.integer _ _ 
   (valuation.integer.integers v) π h,
  erw [is_uniformizer, h1] at hπ,
  exact ne_of_gt of_add_neg_one_le_one hπ,
end

lemma uniformizer_valuation_lt_one {π : K₀} (hπ : is_uniformizer v (π : K)) : v (π : K) < 1 := 
(valuation.integer.not_is_unit_iff_valuation_lt_one π).mp (uniformizer_not_is_unit v hπ)

variable [is_discrete v]

lemma exists_uniformizer : ∃ π : K₀, is_uniformizer v (π : K) := 
begin
  letI surj_v : is_discrete v, apply_instance,
  refine ⟨⟨(surj_v.surj (multiplicative.of_add (- 1 : ℤ) : ℤₘ₀)).some, _⟩, 
    (surj_v.surj (multiplicative.of_add (- 1 : ℤ) : ℤₘ₀)).some_spec⟩,
  rw [mem_integer, (surj_v.surj (multiplicative.of_add (- 1 : ℤ) : ℤₘ₀)).some_spec],
  exact (le_of_lt of_add_neg_one_le_one),
end

instance : nonempty (uniformizer v) := 
⟨⟨(exists_uniformizer v).some, (exists_uniformizer v).some_spec⟩⟩

variables (π : uniformizer v) {K}

lemma pow_uniformizer /- {π : K₀} (hπ : is_uniformizer v (π : K)) -/ {r : K₀} (hr : r ≠ 0) : 
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
  { rw [valuation.map_mul, map_zpow₀,π.2, of_add_neg, coe_inv, inv_zpow', neg_neg,
      ← with_zero.coe_zpow, ← int.of_add_mul, one_mul, of_add_neg, of_add_to_add, 
      coe_inv, coe_unzero, inv_mul_cancel hr₀], },
  set a : K₀ := ⟨π.1^(-m )*r, by apply le_of_eq hpow⟩ with ha,
  have ha₀ : (↑a : K) ≠ 0, 
  { simp only [ha, neg_neg, set_like.coe_mk, ne.def],
    by_cases h0 : to_add (unzero hr₀) = 0,
    { rw [h0, zpow_zero, one_mul, subring.coe_eq_zero_iff], exact hr },
    { apply mul_ne_zero,
      { rw [ne.def, zpow_eq_zero_iff h0, subring.coe_eq_zero_iff],
        exact uniformizer_ne_zero' v π},
      { rw [ne.def, subring.coe_eq_zero_iff], exact hr, }}},
  have h_unit_a : is_unit a,
  { exact integers.is_unit_of_one (integer.integers v) ((is_unit_iff_ne_zero).mpr ha₀) hpow },
  use h_unit_a.unit,
  ext,
  rw [is_unit.unit_spec, subring.coe_mul, subring.coe_pow, subtype.coe_mk, hn],
  rw ← mul_assoc,
  --rw ← zpow_coe_nat,
  --rw ← zpow_add,
  rw [zpow_neg, zpow_coe_nat],
  rw mul_inv_cancel, rw one_mul,
  sorry,
end

lemma ideal_is_principal (I : ideal K₀) : I.is_principal:=
begin
  classical,
  have π := (uniformizer.nonempty v).some,
  by_cases hI : I = ⊥,
  {rw hI, exact bot_is_principal},
  { rw ← ne.def at hI,
    obtain ⟨x, ⟨hx_mem, hx₀⟩⟩ := submodule.exists_mem_ne_zero_of_ne_bot hI,
    let P : ℕ → Prop := λ n, π.1^n ∈ I,
    have H : ∃ n, P n,
    { obtain ⟨n, ⟨u, hu⟩⟩ := pow_uniformizer v π hx₀,
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
      { obtain ⟨m, ⟨u, hu⟩⟩ := pow_uniformizer v π hr₀,
        rw submodule_span_eq,
        rw mem_span_singleton',
        use u * π.1^(m - N),
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
  obtain ⟨π, hπ⟩ := exists_uniformizer v,
  rintros ⟨-, -, h⟩,
  specialize h (uniformizer_ne_zero v hπ),
  rw ← is_unit_iff_exists_inv at h,
  exact uniformizer_not_is_unit v hπ h,
end

lemma is_principal_ideal_ring : is_principal_ideal_ring K₀:= 
⟨λ I, ideal_is_principal v I⟩

lemma integer_is_local_ring : local_ring K₀ :=
{ exists_pair_ne := ⟨0, 1, zero_ne_one⟩,
  is_unit_or_is_unit_of_add_one := λ a b hab, 
  begin
    by_cases ha : is_unit a,
    { exact or.inl ha },
    { right,
      have hab' : v (a + b : K) = 
        (1 : ℤₘ₀),
      { rw [← subring.coe_add, hab, subring.coe_one, valuation.map_one] },
      have hb : (↑b : K) ≠ 0, sorry,
      apply @integers.is_unit_of_one K _ _ _ v K₀ _ _ (integer.integers v) b
        ((is_unit_iff_ne_zero).mpr hb) _,
      have hab'' : v a < (1 : ℤₘ₀),
      { apply lt_of_le_of_ne,
        apply a.2,
        sorry },
      change v ↑b = 1,
      replace hab'' : v (-a) < v (a + b), sorry,
      rw [← add_sub_cancel' (↑a : K) ↑b],
      rw sub_eq_add_neg,
      rw [add_comm (↑a + ↑b) _],
      rw add_eq_max_of_ne (ne_of_lt hab''),
      sorry },
  end }

end discrete_valuation

namespace disc_valued

open discrete_valuation

variables (K : Type*) [field K] [hv : valued K ℤₘ₀] 

local notation `K₀` := hv.v.integer

def is_uniformizer := discrete_valuation.is_uniformizer hv.v

def uniformizer := discrete_valuation.uniformizer hv.v

instance [hv : valued K ℤₘ₀] [is_discrete hv.v] : nonempty (uniformizer K) := 
⟨⟨(exists_uniformizer hv.v).some, (exists_uniformizer hv.v).some_spec⟩⟩

variables [is_discrete hv.v]

instance is_principal_ideal_ring : is_principal_ideal_ring K₀ := 
discrete_valuation.is_principal_ideal_ring hv.v

instance : local_ring K₀ := discrete_valuation.integer_is_local_ring hv.v

-- Chapter I, Section 1, Proposition 1 in Serre's Local Fields
instance discrete_valuation_ring : discrete_valuation_ring K₀ := 
  ((discrete_valuation_ring.tfae K₀ (not_is_field hv.v)).out 0 4).mpr $ 
  (ideal_is_principal hv.v) _

end disc_valued