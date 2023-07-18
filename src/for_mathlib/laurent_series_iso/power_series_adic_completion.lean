import algebra.group.with_one.units
import with_zero
import for_mathlib.laurent_series_iso.old_power_series_adic_completion
import topology.uniform_space.abstract_completion

-- topology.metric_space.cau_seq_filter

noncomputable theory

open uniform_space power_series abstract_completion is_dedekind_domain.height_one_spectrum polynomial
open_locale discrete_valuation

namespace completion_laurent_series

variables (K : Type*) [field K]

def power_series.ideal_X (K : Type*) [field K] : is_dedekind_domain.height_one_spectrum 
  (power_series K) := 
{ as_ideal := ideal.span({X}),
  is_prime := power_series.span_X_is_prime,
  ne_bot   := by { rw [ne.def, ideal.span_singleton_eq_bot], exact X_ne_zero }} 

instance : valued (laurent_series K) ℤₘ₀ := valued.mk' (power_series.ideal_X K).valuation

section complete

open filter topological_space laurent_series
open_locale filter topology uniformity

def coeff_map (d : ℤ) : laurent_series K → K := λ x, x.coeff d

-- def val_equiv : (hahn_series.add_val ℤ K).valuation.is_equiv valued.v := sorry

-- lemma vecchio_int (f : power_series K) :
--   ((power_series.ideal_X K).int_valuation f)  =
--   ↑(multiplicative.of_add (- (↑f : (hahn_series ℕ K)).order : ℤ)) := sorry
/-
* In the hahn_series.lean file there are things like `order_mul`, `order_neg`, `order_zero`,
  `order_single`, `order_C`; more globally, there is `add_val` defined as the order, showing that it
  is an `add_val`. It takes values (for Laurent Series) in `with_zero ℤ`.
* The `order_div` and `order_inv` are called with `fae_` and are in **old**
* There is also a lemma `order_eq_of_power_series` in **old**, showing that the "orders" of a
*power_series* (one obtained by seeing it as a hahn series, the other by using the `part_enat` def
that is basically the same but that has more API, eg about being divisible by `X^n`) coincide. The
above lemma is stated in terms of `part_enat`, and there is `order_eq_of_power_series_Z` that shows 
that the equality stay true if (1) seeing the power series as a laurent series; and (2) going to `ℤ`
* Read lines *257-265*
-/

-- lemma aux₁ {R : Type*} [comm_semiring R] {φ : power_series R} : --(hφ : φ ≠ 0) :
--   (((↑φ : (hahn_series ℕ R)).order) : ℤ) = (hahn_series.of_power_series ℤ R φ).order := sorry

-- lemma aux₂ {f : laurent_series K} {P Q : power_series K} {hQ : Q ∈ non_zero_divisors (power_series K)}
--   (hfPQ : is_localization.mk' (laurent_series K) P ⟨Q, hQ⟩ = f) :
--     hahn_series.order f = (↑P : (hahn_series ℕ K)).order - (↑Q : (hahn_series ℕ K)).order :=
-- begin
--   rw aux₁,
--   rw aux₁,
--   rw ← fae_order_div,
--   rw ← hfPQ,
--   simp only [is_fraction_ring.mk'_eq_div, laurent_series.coe_algebra_map, set_like.coe_mk],
--   sorry,--needed?
--   -- have := non_zero_divisors.ne_zero hQ,
--   rw ← (hahn_series.of_power_series ℤ K).map_zero,
--   apply hahn_series.of_power_series_injective.ne (non_zero_divisors.ne_zero hQ),
-- end

-- lemma vecchio (f : laurent_series K) : (valued.v f)⁻¹ = ↑(multiplicative.of_add (f.order)) := 
-- begin
--   obtain ⟨P, ⟨Q, hQ, hfPQ⟩⟩ := @is_fraction_ring.div_surjective (power_series K) _ _
--     (laurent_series K) _ _ _ f,
--   replace hfPQ : is_localization.mk' (laurent_series K) P ⟨Q, hQ⟩ = f :=
--     by simp only [hfPQ, is_fraction_ring.mk'_eq_div, set_like.coe_mk],
--   -- have hP : P ≠ 0 :=  by sorry,--{rw ← hfPQ at hf, exact is_localization.ne_zero_of_mk'_ne_zero hf},
--   -- have hQ₀ : Q ≠ 0 := by rwa [← mem_non_zero_divisors_iff_ne_zero],
--   have val_P_Q := @valuation_of_mk' (power_series K) _ _ _ (laurent_series K) _ _ _
--     (power_series.ideal_X K) P ⟨Q, hQ⟩,
--   rw hfPQ at val_P_Q,
--   rw inv_eq_iff_eq_inv,
--   erw val_P_Q,
--   rw vecchio_int,
--   rw vecchio_int,
--   rw ← with_zero.coe_div,
--   rw ← with_zero.coe_inv,
--   rw with_zero.coe_inj,
--   rw ← of_add_sub,
--   rw ← of_add_neg,
--   apply congr_arg,
--   rw ← neg_sub',
--   rw ← neg_eq_iff_eq_neg,
--   rw neg_neg,
--   simp only [set_like.coe_mk],
--   exact (aux₂ K hfPQ).symm,
-- end

lemma vecchio_int {n d : ℕ} {f : power_series K} (H : valued.v (f : laurent_series K) ≤
  ↑(multiplicative.of_add ((- d) : ℤ))) : n < d → coeff K n f = 0 :=
begin
  intro hnd,
  convert (@power_series.X_pow_dvd_iff K _ d f).mp _ n hnd,
  have := @valuation_of_algebra_map (power_series K) _ _ _ (laurent_series K) _ _ _
    (power_series.ideal_X K) f,--togliere `@`
  erw this at H,
  have dvd_val_int := (@int_valuation_le_pow_iff_dvd (power_series K) _ _ _ (power_series.ideal_X K)
    f d).mp H,
  rw [← span_singleton_dvd_span_singleton_iff_dvd, ← ideal.span_singleton_pow],
  apply dvd_val_int,
end

lemma vecchio {n D : ℤ} {f : laurent_series K} (H : valued.v f ≤ ↑(multiplicative.of_add (- D))) :
  n < D → coeff_map K n f = 0 :=
begin
  intro hnd,
  rw [coeff_map],--I wonder if `coeff_map` is a good ide
  by_cases h_n_ord : n < f.order,
  { exact hahn_series.coeff_eq_zero_of_lt_order h_n_ord },
  { rw not_lt at h_n_ord,
    set F := power_series_part f with hF, --non proprio necessaria
    have ord_neg : f.order ≤ 0, sorry,--andrà fatto `by_cases` usando che se no `vecchio_int` basta
    obtain ⟨s, hs⟩ := int.exists_eq_neg_of_nat ord_neg,
    have F_mul := of_power_series_power_series_part f,
    rw [hs] at h_n_ord,
    rw [← hF, hs, neg_neg, ← hahn_series.of_power_series_X_pow s, ← coe_power_series,
      ← coe_power_series] at F_mul,
    obtain ⟨m, hm⟩ := int.eq_coe_of_zero_le (neg_le_iff_add_nonneg.mp h_n_ord),
    have hD : 0 ≤  D + s, sorry,
    obtain ⟨d, hd⟩ := int.eq_coe_of_zero_le hD,
    have F_coeff := power_series_part_coeff f m,
    rw [hs, add_comm, ← eq_add_neg_of_add_eq hm, ← hF] at F_coeff,
    simp only,
    rw [← F_coeff],--I wonder if `coeff_map` is a good idea
    apply @vecchio_int K _ m d F,
    { rw F_mul,
      rw map_mul,
      rw ← hd,
      simp only [power_series.coe_pow, /- valuation.map_pow,  -/neg_add_rev, of_add_add,/-  of_add_neg, -/
        with_zero.coe_mul/- , with_zero.coe_inv -/],
      have temp : valued.v ((↑power_series.X : (laurent_series K)) ^ s) = 
        ↑(multiplicative.of_add (- (s : ℤ))), sorry,
      rw temp,
      have temp₁ : ↑(multiplicative.of_add (-↑s)) ≠ (0 : ℤₘ₀), sorry,
      exact (mul_le_mul_left₀ temp₁).mpr H,
    },
    have at_least : m ≤ d, 
    rw [← int.coe_nat_le, ← hd, ← hm],
    linarith,
    sorry--e' falso perche' devo risolvere `≤` **vs** `<`.
  }
end


-- #exit

lemma eq_coeff_of_val_sub_lt {d n : ℤ} {f g : laurent_series K} 
  (H : valued.v (g - f) ≤ ↑(multiplicative.of_add (- d))) :
  n < d → coeff_map K n g = coeff_map K n f :=
begin
  by_cases triv : g = f,
  { exact (λ _, by rw triv) },
  { intro hn,
    apply eq_of_sub_eq_zero,
    erw [← hahn_series.sub_coeff],
    apply vecchio K H hn,



    -- apply hahn_series.coeff_eq_zero_of_lt_order,
    -- suffices : d < (g - f).order,
    -- { exact lt_of_le_of_lt hn this },
    -- { rw [← multiplicative.of_add_lt, ← with_zero.coe_lt_coe],
    --   replace triv : (valued.v (g - f) ≠ (0 : ℤₘ₀)),
    --   { exact (valuation.ne_zero_iff _).mpr (sub_ne_zero_of_ne triv) },
    --   rw [of_add_neg, ← with_zero.coe_unzero triv, with_zero.coe_lt_coe, lt_inv', 
    --     ← with_zero.coe_lt_coe, with_zero.coe_inv, with_zero.coe_unzero triv] at H,
        
        
         }
end

lemma uniform_continuous_coeff_map {uK : uniform_space K} (h : uniformity K = 𝓟 id_rel) (d : ℤ) :
  uniform_continuous (coeff_map K d) :=
begin
  refine uniform_continuous_iff_eventually.mpr (λ S hS, eventually_iff_exists_mem.mpr _),
  let γ : ℤₘ₀ˣ := units.mk0 (↑(multiplicative.of_add (- (d + 1)))) with_zero.coe_ne_zero,
  use {P | valued.v (P.snd - P.fst) < ↑γ},
  refine  ⟨(valued.has_basis_uniformity (laurent_series K) ℤₘ₀).mem_of_mem (by tauto), λ P hP, _⟩,
  rw [h] at hS,
  apply hS,
  rw [eq_coeff_of_val_sub_lt K (le_of_lt hP) (lt_add_one _), mem_id_rel],
end

/- The definition below avoids the assumption that `K` be endowed with the trivial uniformity,
  rather putting this in the proof.
-/
variable {K}
def cauchy.coeff_map' {ℱ : filter (laurent_series K)} (hℱ : cauchy ℱ) : ℤ → K :=
begin
  letI : uniform_space K := ⊥,
  have hK : @uniformity K ⊥ = filter.principal id_rel := rfl,
  use λ d, cauchy_discrete_is_constant hK (hℱ.map (uniform_continuous_coeff_map K hK d)),
end

lemma aux_coeff_map' {ℱ : filter (laurent_series K)} (hℱ : cauchy ℱ) (D : ℤ) : 
  tendsto (coeff_map K D) ℱ (𝓟 {cauchy.coeff_map' hℱ D}) :=
begin
  letI : uniform_space K := ⊥,
  have hK : uniformity K = filter.principal id_rel, refl,
  exact cauchy_discrete_le hK (hℱ.map (uniform_continuous_coeff_map K hK D)),
end

lemma bounded_supp_of_val_le (f : laurent_series K) (d : ℤ) : ∃ N : ℤ,
∀ (g : laurent_series K), valued.v (g - f) ≤ ↑(multiplicative.of_add (- d)) →
  ∀ n < N, coeff_map K n g = 0 :=
begin
  by_cases hf : f = 0,
  { refine ⟨d, λ _ hg _ hn, _⟩,
    simpa only [eq_coeff_of_val_sub_lt K hg hn, hf] using hahn_series.zero_coeff },
  { refine ⟨min (f.2.is_wf.min (hahn_series.support_nonempty_iff.mpr hf)) d - 1, λ _ hg n hn, _⟩,
    have hn' : coeff_map K n f = 0 := function.nmem_support.mp ( λ h, set.is_wf.not_lt_min
      f.2.is_wf (hahn_series.support_nonempty_iff.mpr hf) h _),
    rwa eq_coeff_of_val_sub_lt K hg _,
    { exact lt_trans hn (int.lt_of_le_sub_one $ (sub_le_sub_iff_right _).mpr (min_le_right _ d)) },
    { exact lt_trans hn (int.lt_of_le_sub_one $ (sub_le_sub_iff_right _).mpr (min_le_left _ _)) }},
end

lemma cauchy.bot₁ {ℱ : filter (laurent_series K)} (hℱ : cauchy ℱ) : ∃ N, 
  ∀ᶠ y in ℱ, ∀ n < N, coeff_map K n y = (0 : K) :=
begin
  let entourage := {P : (laurent_series K) × (laurent_series K) | valued.v (P.snd - P.fst)
    < ↑(multiplicative.of_add (0 : ℤ))},
  let ζ : ℤₘ₀ˣ := units.mk0 (↑(multiplicative.of_add 0)) with_zero.coe_ne_zero,
  obtain ⟨S, ⟨hS, ⟨T, ⟨hT, H⟩⟩⟩⟩ := mem_prod_iff.mp (filter.le_def.mp hℱ.2 entourage
    (@has_basis.mem_of_mem _ _ _ _ _ ζ ((valued.has_basis_uniformity (laurent_series K) ℤₘ₀)) _)),
  obtain ⟨f, hf⟩ := forall_mem_nonempty_iff_ne_bot.mpr hℱ.1 (S ∩ T)
    (by {exact inter_mem_iff.mpr ⟨hS, hT⟩}),
  obtain ⟨N, hN⟩ := bounded_supp_of_val_le f 0,
  use N,
  apply mem_of_superset (inter_mem hS hT),
  suffices : (S ∩ T) ×ˢ (S ∩ T) ⊆ entourage,
  { intros g hg,
    have h_prod : (f, g) ∈ entourage,
    { refine this (set.mem_prod.mpr _),
      exact ⟨hf, hg⟩ },
    exact (λ _ hn, hN g (le_of_lt h_prod) _ hn) },
  exacts [(set.prod_mono (set.inter_subset_left S T) (set.inter_subset_right S T)).trans H, trivial]
end

lemma cauchy.bot_aux {ℱ : filter (laurent_series K)} (hℱ : cauchy ℱ) : ∃ N, 
  ∀ n < N, ℱ.map (coeff_map K n) ≤ filter.principal {0} :=
begin
  simp only [principal_singleton, pure_zero, nonpos_iff, mem_map],
  obtain ⟨N, hN⟩ := hℱ.bot₁,
  use  N,
  intros n hn,
  apply filter.mem_of_superset hN,
  intros a ha,
  exact ha n hn,
end

lemma cauchy.bot₂ {ℱ : filter (laurent_series K)} (hℱ : cauchy ℱ) : ∃ N, ∀ n,
  n < N → (hℱ.coeff_map' n) = 0 :=
begin
  letI : uniform_space K := ⊥,
  have hK : uniformity K = filter.principal id_rel, refl,
  obtain ⟨N, hN⟩ := hℱ.bot_aux,
  use N,
  intros n hn,
  refine ne_bot_unique_principal hK (hℱ.map (uniform_continuous_coeff_map K hK n)).1
    (aux_coeff_map' _ _) (hN n hn),
end

/-- The following lemma shows that for every `d` smaller than the minimum between the integers
produced in `cauchy.bot₁` and `cauchy.bot₂`, for almost all series in `ℱ` the `d`th coefficient
coincides with the `d`th coefficient of `hℱ.coeff_map'`.
-/
-- lemma cauchy.bot₃ {ℱ : filter (laurent_series K)} (hℱ : cauchy ℱ) :
--   ∀ᶠ f in ℱ, ∀ d ≤ linear_order.min hℱ.bot₁.some hℱ.bot₂.some, 
lemma cauchy.bot₃ {ℱ : filter (laurent_series K)} (hℱ : cauchy ℱ) : ∃ N,
  ∀ᶠ f in ℱ, ∀ d < N, (hℱ.coeff_map' d) = coeff_map K d f :=
begin
  obtain ⟨⟨N₁, hN₁⟩, ⟨N₂, hN₂⟩⟩ := ⟨hℱ.bot₁, hℱ.bot₂⟩,
  refine ⟨min N₁ N₂, ℱ.3 hN₁ (λ _ hf d hd, _)⟩,
  rw [hf d (lt_of_lt_of_le hd (min_le_left _ _)), hN₂ d (lt_of_lt_of_le hd (min_le_right _ _))],
end

lemma cauchy.coeff_map_support_bdd'' {ℱ : filter (laurent_series K)} (hℱ : cauchy ℱ) :
  bdd_below (hℱ.coeff_map'.support) :=
begin
  refine ⟨hℱ.bot₂.some, λ d hd, _⟩,
  by_contra' hNd,
  exact hd (hℱ.bot₂.some_spec d hNd),
end

def cauchy.mk_laurent_series {ℱ : filter (laurent_series K)} (hℱ : cauchy ℱ) : (laurent_series K) :=
hahn_series.mk (λ d, hℱ.coeff_map' d)
  (set.is_wf.is_pwo (hℱ.coeff_map_support_bdd''.well_founded_on_lt))

/-
`COPIATA DA SOPRA`
lemma eventually_constant {uK : uniform_space K} (h : uniformity K = 𝓟 id_rel)
  {ℱ : filter (ratfunc K)} (hℱ : cauchy ℱ) (n : ℤ) :
  ∀ᶠ x in ℱ, ratfunc.coeff x n = cauchy_discrete_is_constant h 
    (hℱ.map (uniform_continuous_coeff_map h n)) := by simpa only [comap_principal, le_principal_iff]
    using tendsto.le_comap (cauchy_discrete_converges _ (hℱ.map (uniform_continuous_coeff_map _ _)))
    -/
open_locale big_operators


lemma set_inter_Iio {α β: Type*} [linear_order β] {X : β → set α} {D N : β} (hND : N ≤ D) :
  (⋂ d ∈ (set.Iio D), X d) = (⋂ d ∈ (set.Iio N), X d) ∩ (⋂ d ∈ (set.Ico N D), X d) :=
begin
  by_cases hND₀ : N = D,
  { rw hND₀,
    simp only [set.mem_Iio, set.mem_Ico],
    have aux : (⋂ d ∈ {d | D ≤ d ∧ d < D}, X d) = set.univ,
    have := @set.bInter_empty β α X,
    apply set.Inter_congr,
    -- have auxx : {x | D ≤ x ∧ x < D} = ∅, sorry,
    -- -- rw aux,
    -- have := @set.bInter_empty β α X,
    

  },
  { replace hND := lt_of_le_of_ne hND hND₀,
    rw [← set.Inter_inter_distrib, ← max_eq_right (le_refl D), ← set.Iio_union_Ioo
      (min_lt_of_left_lt hND), max_eq_right (le_refl D)],
    congr' with d,
    simp only [set.mem_union, set.mem_Iio, set.mem_Ico, set.mem_Ioo, set.mem_Inter,
      set.mem_inter_iff, and_imp],
    refine ⟨λ h, ⟨λ H, h $ or.inl $ H.trans hND, λ H h_ND, h $ or.inl h_ND⟩,
      λ h H, _⟩,
    rcases H with Ha | Hb,
    by_cases H_Nd : d < N,
    exacts [h.1 H_Nd, h.2 (le_of_not_lt H_Nd) Ha, h.2 (le_of_lt Hb.1) Hb.2] },
end


lemma cauchy.eventually₁ {ℱ : filter (laurent_series K)} (hℱ : cauchy ℱ) :
  ∀ D : ℤ, ∀ᶠ f in ℱ, ∀ d, d < D → (hℱ.coeff_map' d) = coeff_map K d f := 
begin
  intro D,
  set X : ℤ → set (laurent_series K) := λ d, {f | (hℱ.coeff_map' d) = coeff_map K d f} with hX,
  have intersec : (⋂ n ∈ (set.Iio D), X n) ⊆ {x : laurent_series K | ∀ (d : ℤ), d < D 
    → hℱ.coeff_map' d = coeff_map K d x},
  { rintro (_ hf n hn),
    simp only [set.mem_Inter, set.mem_set_of_eq, hX] at hf,
    exact hf n hn, },
  set N := min hℱ.bot₃.some D with hN₀,
  suffices : (⋂ n ∈ (set.Iio D), X n) ∈ ℱ,
  exact ℱ.3 this intersec,
  by_cases H : D < hℱ.bot₃.some,
  { apply ℱ.3 hℱ.bot₃.some_spec,
    simp only [set.mem_Iio, set.subset_Inter₂_iff, set.set_of_subset_set_of],
    intros m hm f hd,
    exact hd _ (lt_trans hm H)},
  { rw [set_inter_Iio (min_le_right N D), filter.inter_mem_iff, min_eq_left (min_le_right _ _),
    ← hN₀],
    split,
    { rw [hN₀, min_eq_left (not_lt.mp H), hX],
      convert hℱ.bot₃.some_spec,
      ext f,
      simpa only [set.mem_Inter, set.mem_set_of_eq, set.mem_set_of_eq]},
    { have : (⋂ (n : ℤ) (H : n ∈ set.Ico N D), X n) = ⋂ (n : ((finset.Ico N D) : (set ℤ))), X n,
      { simp only [set.mem_Ico, set.Inter_coe_set, finset.mem_coe, finset.mem_Ico, subtype.coe_mk]},
      simp only [this, filter.Inter_mem],
      intro d,
      apply aux_coeff_map' hℱ,
      simpa only [principal_singleton, mem_pure] using rfl }}
end

lemma diff.eventually₀ {f g : (laurent_series K)} {D : ℤ}
  (H : ∀ d, d < D → coeff_map K d g = coeff_map K d f) :
  valued.v (f - g) ≤ ↑(multiplicative.of_add D) :=
begin
  sorry,--`FAE` Temo sia falso col `valued.v (f - g) < ↑(multiplicative.of_add D)`, probabilmente
    -- vero con `≤` ma rompe la prova di `cauchy.eventually₂`.
end

lemma cauchy.eventually₂ {ℱ : filter (laurent_series K)} (hℱ : cauchy ℱ)
  {U : set (laurent_series K)} (hU : U ∈ 𝓝 (hℱ.mk_laurent_series)) : ∀ᶠ f in ℱ, f ∈ U := 
begin
  obtain ⟨γ, hU₁⟩ := valued.mem_nhds.mp hU,
  suffices : ∀ᶠ f in ℱ, f ∈ {y : laurent_series K | valued.v (y - hℱ.mk_laurent_series) < ↑γ},
  { apply this.mono (λ _ hf, hU₁ hf) },
  { set D := multiplicative.to_add (with_zero.unzero γ.ne_zero) - 1 with hD₀,
    have hD : ((multiplicative.of_add D) : ℤₘ₀) < γ,
    { rw [← with_zero.coe_unzero γ.ne_zero, with_zero.coe_lt_coe],
      apply int.lt_of_le_sub_one (le_of_eq (refl _)) },
    apply (hℱ.eventually₁ D).mono,
    intros f hf,
    apply lt_of_le_of_lt (diff.eventually₀ _) hD,
    apply hf },
end

instance : complete_space (laurent_series K) :=
  ⟨λ _ hℱ, ⟨hℱ.mk_laurent_series, λ S hS, hℱ.eventually₂ hS⟩⟩

end complete

section dense 

lemma coe_range_dense : dense_range (coe : (ratfunc K) → (laurent_series K)) := sorry

end dense

section boh

local attribute [instance] classical.prop_decidable
open multiplicity unique_factorization_monoid

lemma polynomial.norm_unit_X : norm_unit (polynomial.X : (polynomial K)) = 1 :=
begin
  have := @coe_norm_unit K _ _ _ polynomial.X,
  rwa [leading_coeff_X, norm_unit_one, units.coe_one, map_one, units.coe_eq_one] at this,
end

lemma polynomial.X_eq_normalize : (polynomial.X : (polynomial K)) = normalize polynomial.X :=
  by simp only [normalize_apply, polynomial.norm_unit_X, units.coe_one, mul_one]

lemma power_series.norm_unit_X : norm_unit (power_series.X : (power_series K)) = 1 :=
  by {dsimp only [norm_unit],rw [inv_eq_one, ← units.coe_eq_one, unit_of_divided_by_X_pow_nonzero,
    divided_by_X_pow_of_X_eq_one]}

lemma power_series.X_eq_normalize : (power_series.X : (power_series K)) = normalize power_series.X :=
  by simp only [normalize_apply, power_series.norm_unit_X, units.coe_one, mul_one]

lemma aux_old_pol (P : (polynomial K)) (hP : P ≠ 0) : 
  (normalized_factors (ideal.span {↑P})).count (power_series.ideal_X K).as_ideal =
  (normalized_factors (ideal.span {P})).count (ideal.span {polynomial.X} : ideal (polynomial K)) :=
begin
  have for_pol := principal_ideal_ring.count_normalized_factors_eq_count_normalized_factors_span hP
    polynomial.X_ne_zero (polynomial.norm_unit_X K) polynomial.prime_X,
  rw [← for_pol],
  have for_pow := principal_ideal_ring.count_normalized_factors_eq_count_normalized_factors_span
    (coe_ne_zero hP) power_series.X_ne_zero (power_series.norm_unit_X K) power_series.X_prime,
  erw [← for_pow],
  have aux_pol := @multiplicity_eq_count_normalized_factors (polynomial K) _ _ _ _ _ _ polynomial.X P
    (irreducible_X) hP,
  have aux_pow_series := @multiplicity_eq_count_normalized_factors (power_series K) _ _ _ _ _ _ power_series.X
    ↑P (prime.irreducible power_series.X_prime) (coe_ne_zero hP),
  apply nat.le_antisymm,
  { rw [polynomial.X_eq_normalize, power_series.X_eq_normalize, ← part_enat.coe_le_coe, ← aux_pol, 
      ← multiplicity.pow_dvd_iff_le_multiplicity, polynomial.X_pow_dvd_iff],
    intros d hd,
    replace aux_pow_series := le_of_eq aux_pow_series.symm,
    rw [← multiplicity.pow_dvd_iff_le_multiplicity, power_series.X_pow_dvd_iff] at aux_pow_series,
    replace aux_pow_series := aux_pow_series d hd,
    rwa [polynomial.coeff_coe P d] at aux_pow_series },
  { rw [polynomial.X_eq_normalize, power_series.X_eq_normalize, ← part_enat.coe_le_coe, ← aux_pow_series, 
      ← multiplicity.pow_dvd_iff_le_multiplicity, power_series.X_pow_dvd_iff],
    intros d hd,
    replace aux_pol := le_of_eq aux_pol.symm,
    rw [← multiplicity.pow_dvd_iff_le_multiplicity, polynomial.X_pow_dvd_iff] at aux_pol,
    replace aux_pol := aux_pol d hd,
    rwa [← polynomial.coeff_coe P d] at aux_pol },
end


lemma should_be_in_old_pol (P : (polynomial K)) : (ideal_X K).int_valuation (P) =
  (power_series.ideal_X K).int_valuation (↑P : (power_series K)) :=
begin
  by_cases hP : P = 0,
  { rw [hP, valuation.map_zero, polynomial.coe_zero, valuation.map_zero] },
  { simp only [fae_int_valuation_apply],
    rw [int_valuation_def_if_neg _ hP, int_valuation_def_if_neg _ $ coe_ne_zero hP],
    simp only [ideal_X_span, of_add_neg, inv_inj, with_zero.coe_inj, embedding_like.apply_eq_iff_eq,
      nat.cast_inj],
    have span_ne_zero : (ideal.span {P} : ideal (polynomial K)) ≠ 0 ∧
    (ideal.span {polynomial.X} : ideal (polynomial K)) ≠ 0 := by simp only [ideal.zero_eq_bot,
    ne.def, ideal.span_singleton_eq_bot, hP, polynomial.X_ne_zero, not_false_iff, and_self],
    have span_X_prime : (ideal.span {polynomial.X} : ideal (polynomial K)).is_prime,
    { apply (@ideal.span_singleton_prime (polynomial K) _ _ polynomial.X_ne_zero).mpr prime_X },
    have := @count_normalized_factors_eq_associates_count K _ (ideal.span {P})
    (ideal.span {polynomial.X}) span_ne_zero.1 ((@ideal.span_singleton_prime (polynomial K) _ _ 
    polynomial.X_ne_zero).mpr prime_X) span_ne_zero.2,
    convert this.symm,

    have span_ne_zero' : (ideal.span {↑P} : ideal (power_series K)) ≠ 0 ∧
    ((power_series.ideal_X K).as_ideal : ideal (power_series K)) ≠ 0 := by simp only [ne.def, 
      ideal.zero_eq_bot, ideal.span_singleton_eq_bot, coe_ne_zero hP, power_series.X_ne_zero,
      not_false_iff, and_self, (power_series.ideal_X K).3],
    have also := @count_normalized_factors_eq_associates_count' K _ (ideal.span {↑P})
    (power_series.ideal_X K).as_ideal span_ne_zero'.1 (power_series.ideal_X K).2 span_ne_zero'.2,
    rw [← aux_old_pol _ _ hP],
    convert also.symm,
  }
end

open ratfunc


lemma ovvio (f : (polynomial K)) (g : (polynomial K)) (hg : g ≠ 0) : (ratfunc.mk f g) = 
  is_localization.mk' (ratfunc K) f ⟨g, mem_non_zero_divisors_iff_ne_zero.2 hg⟩ :=
by simp only [mk_eq_div, is_fraction_ring.mk'_eq_div, set_like.coe_mk]

lemma ovvio' (f : (polynomial K)) (g : polynomial K) (hg : g ≠ 0) : 
  (ideal_X K).valuation ( ratfunc.mk f g) =
  ((ideal_X K).int_valuation f) / ((ideal_X K).int_valuation g) :=
by simp only [ovvio _ _ _ hg, valuation_of_mk', set_like.coe_mk]

lemma ratfunc.coe_coe (f : polynomial K) : (↑(algebra_map (polynomial K) (ratfunc K) f) :
  (laurent_series K)) = (algebra_map (power_series K) (laurent_series K)) f :=
by {rw [ratfunc.coe_def, coe_alg_hom, lift_alg_hom_apply, denom_algebra_map f, map_one, div_one,
  num_algebra_map], refl}


lemma should_be_in_old' (P: (ratfunc K)) : (ideal_X K).valuation (P) =
  (power_series.ideal_X K).valuation ((↑P : (laurent_series K))) :=
begin
  apply ratfunc.induction_on' P,
  intros f g h,
  convert ovvio' K f g h,
  rw ovvio K f g h,
  have aux : (↑(is_localization.mk' (ratfunc K) f ⟨g, mem_non_zero_divisors_iff_ne_zero.2 h⟩) : 
    laurent_series K) = ((is_localization.mk' (laurent_series K) (↑f : (power_series K))
    ⟨g, mem_non_zero_divisors_iff_ne_zero.2 $ coe_ne_zero h⟩) : laurent_series K),
  { simp only [is_fraction_ring.mk'_eq_div, set_like.coe_mk, coe_div],
    congr;
    apply ratfunc.coe_coe K,
   },
  rw aux,
  have := @valuation_of_mk' (power_series K) _ _ _ (laurent_series K) _ _ _
    (power_series.ideal_X K) ↑f ⟨g, mem_non_zero_divisors_iff_ne_zero.2 $ coe_ne_zero h⟩,
  convert this;
  apply should_be_in_old_pol,
end


lemma should_be_in_old (P₁ P₂ : (ratfunc K)) : valued.v (P₁ - P₂) =
  valued.v ((↑P₁ : (laurent_series K)) - ↑P₂) :=
begin
  have : valued.v (P₁ - P₂) = (ideal_X K).valuation (P₁ - P₂),
  refl,
  rw [this, should_be_in_old', ratfunc.coe_sub],
  refl,
end

-- FAE: The one below is probably the most disgusting proof on earth
lemma coe_is_inducing : uniform_inducing (coe : (ratfunc K) → (laurent_series K)) :=
begin
  rw uniform_inducing_iff,
  rw filter.comap,
  ext S,
  split,
  { intro hS,
    simp only [exists_prop, filter.mem_mk, set.mem_set_of_eq] at hS,
    obtain ⟨T, ⟨hT, pre_T⟩⟩ := hS,
    rw uniformity_eq_comap_nhds_zero at hT ⊢,
    simp only [filter.mem_comap, exists_prop] at hT ⊢,
    obtain ⟨R, ⟨hR, pre_R⟩⟩ := hT,
    obtain ⟨d, hd⟩ := valued.mem_nhds.mp hR,

    use {P : (ratfunc K) | valued.v P < ↑d},
    split,
    { rw valued.mem_nhds,-- questa parentesi e' orribile
      use d,
      simp only [sub_zero],
    },
    { refine subset_trans _ pre_T,
      simp only [set.preimage_set_of_eq],
      rintros ⟨P1, P2⟩ h,
      simp only [set.mem_set_of_eq] at h,
      rw set.mem_preimage,
      simp only,
      apply pre_R,
      simp only [set.mem_preimage],
      apply hd,
      simp only [set.mem_set_of_eq, sub_zero],

      rw ← should_be_in_old,
        --this is the statement that the valuations on pol and laurent ser coincide
      exact h,
    },
  },
  { simp,
    intro hS,
    -- simp at hS,
    rw uniformity_eq_comap_nhds_zero at hS ⊢,
    simp only [filter.mem_comap, exists_prop] at hS ⊢,
    obtain ⟨T, ⟨hT, pre_T⟩⟩ := hS,
    -- simp only [filter.mem_comap],
    obtain ⟨d, hd⟩ := valued.mem_nhds.mp hT,
    let try := {f : (laurent_series K) | valued.v f < ↑d},
    use (λ (x : laurent_series K × laurent_series K), x.snd - x.fst) ⁻¹' try,
    use try,
    { split,
      { rw valued.mem_nhds,-- questa parentesi e' orribile
        use d,
        simp only [sub_zero],
      },
      { simp only [set.preimage_set_of_eq],
      } },
    { simp only [set.preimage_set_of_eq],
      refine subset_trans _ pre_T,
      rintros ⟨P1, P2⟩ h,
      simp only [set.mem_set_of_eq] at h,
      rw set.mem_preimage,
      simp only,
      apply hd,
      simp only [set.mem_set_of_eq, sub_zero],

      rw should_be_in_old,
      exact h,
    },
    
  },
end

lemma unif_cont_coe : uniform_continuous (coe : (ratfunc K) → (laurent_series K)) :=
  (uniform_inducing_iff'.1 (coe_is_inducing K)).1

noncomputable!
def ratfunc_pkg : abstract_completion (ratfunc K) := uniform_space.completion.cpkg 

noncomputable!
def laurent_series_pkg : abstract_completion (ratfunc K) :=
{ space := laurent_series K,
  coe := coe,
  uniform_struct := infer_instance,
  complete := infer_instance,
  separation := infer_instance,
  uniform_inducing := coe_is_inducing K,
  dense := coe_range_dense K}


noncomputable!
def extension_as_ring_hom := uniform_space.completion.extension_hom (coe_alg_hom K).to_ring_hom

noncomputable!
def compare_pkg : (completion_of_ratfunc K) ≃ᵤ laurent_series K :=
  compare_equiv (ratfunc_pkg K) (laurent_series_pkg K)


-- lemma aux (f : ratfunc K) : (f : laurent_series K) = compare_pkg K ↑f :=
--   ((abstract_completion.compare_coe (ratfunc_pkg K) (laurent_series_pkg K) f)).symm

-- lemma extension_eq_compare : (ϕ K (unif_cont_coe K).continuous).to_fun = (compare_pkg K).to_fun :=
--   uniform_space.completion.extension_unique (unif_cont_coe K)
--     (uniform_continuous_compare_equiv _ _) (aux K)

noncomputable! def  laurent_series_ring_equiv : 
  ring_equiv (completion_of_ratfunc K) (laurent_series K) :=
{ map_mul' := (extension_as_ring_hom K (unif_cont_coe K).continuous).map_mul',
  map_add' := (extension_as_ring_hom K (unif_cont_coe K).continuous).map_add',
  .. compare_pkg K }

end boh

end completion_laurent_series