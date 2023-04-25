import complete_dvr

variables {A : Type*} [comm_ring A] 

open_locale discrete_valuation

/- We insist that `v` takes values in ℤₘ₀ in order to define uniformizers as the elements in `K`
whose valuation is exactly `with_zero.multiplicative (- 1) : ℤₘ₀`-/
class is_discrete (v : valuation A ℤₘ₀) :=
(surj : function.surjective v)

open valuation ideal is_dedekind_domain

namespace discrete_valuation

variables [is_domain A] [discrete_valuation_ring A]

instance : valued (fraction_ring A) ℤₘ₀ := sorry

instance : is_discrete (@valued.v (fraction_ring A) _ ℤₘ₀ _ _) := sorry

variables {R : Type*} [comm_ring R] [hR : valued R ℤₘ₀]

/- definition is_uniformizer' (π : hR.v.integer) : Prop := 
  hR.v π = (multiplicative.of_add (- 1 : ℤ) : ℤₘ₀) -/

definition is_uniformizer (π : R) : Prop := 
  hR.v π = (multiplicative.of_add (- 1 : ℤ) : ℤₘ₀)

variables {K : Type*} [field K] [hv : valued K ℤₘ₀]

local notation `K₀` := hv.v.integer

include hv
variable (K)
@[ext]
structure uniformizer :=
(val : hv.v.integer)
(valuation_eq_neg_one : hv.v val = (multiplicative.of_add (- 1 : ℤ) : ℤₘ₀))

--instance t : valued K₀ ℤₘ₀ := sorry

noncomputable
lemma discrete_of_exists_uniformizer {π : K₀} (hπ : is_uniformizer (π : K)) : is_discrete hv.v :=
⟨begin
  intro x,
  apply with_zero.cases_on x,
  {use 0,
    simp only [valuation.map_zero]} ,
  { rw is_uniformizer at hπ,
    intro m,
    use π^(- multiplicative.to_add m),
    rw [map_zpow₀, hπ, ← with_zero.coe_zpow, with_zero.coe_inj, ← of_add_zsmul, ← zsmul_neg', 
      neg_neg,zsmul_one, int.cast_id, of_add_to_add] }
end⟩

variable [is_discrete hv.v]

lemma exists_uniformizer : ∃ π : K₀, is_uniformizer (π : K) := 
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
   
lemma uniformizer_ne_zero {π : K₀} (hπ : is_uniformizer (π : K)) : π ≠ 0 := 
begin
  intro h0,
  rw [h0, is_uniformizer, algebra_map.coe_zero, valuation.map_zero] at hπ,
  exact with_zero.zero_ne_coe hπ,
end

lemma uniformizer_ne_zero' (π : uniformizer K) : π.1 ≠ 0 := 
begin
  intro h0,
  have := π.2,
  rw [h0, algebra_map.coe_zero, valuation.map_zero] at this,
  exact with_zero.zero_ne_coe this,
end

lemma uniformizer_not_is_unit {π : K₀} (hπ : is_uniformizer (π : K)) : ¬ is_unit π := 
begin
  intro h,
  have h1 := @valuation.integers.one_of_is_unit K ℤₘ₀ _ _ hv.v hv.v.integer _ _ 
   (valuation.integer.integers hv.v) π h,
  erw [is_uniformizer, h1] at hπ,
  exact ne_of_gt with_zero.of_add_neg_one_le_one hπ,
end

variables (π : K₀) (hπ : is_uniformizer (π : K))

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
      { rw [← subring.coe_add, hab, subring.coe_one, valuation.map_one] },
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

end discrete_valuation