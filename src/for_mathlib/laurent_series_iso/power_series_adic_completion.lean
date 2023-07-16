import for_mathlib.laurent_series_iso.old_power_series_adic_completion
import topology.uniform_space.abstract_completion
-- topology.metric_space.cau_seq_filter

noncomputable theory

open uniform_space power_series abstract_completion is_dedekind_domain.height_one_spectrum polynomial
open_locale discrete_valuation

-- namespace laurent_series

-- /-The main point of this section is to prove the equality between the X-adic valuation and the order of laurent_series. Applying then `fae_order_eq_val'`, we deduce that for every `f : ratfunc`, the equality of `f : ratfunc` coincides with the valuation of `↑f : laurent_series` -/



-- end laurent_series

namespace completion_laurent_series

variables (K : Type*) [field K]

def power_series.ideal_X (K : Type*) [field K] : is_dedekind_domain.height_one_spectrum 
  (power_series K) := 
{ as_ideal := ideal.span({X}),
  is_prime := power_series.span_X_is_prime,
  ne_bot   := by { rw [ne.def, ideal.span_singleton_eq_bot], exact X_ne_zero }} 

instance : valued (laurent_series K) ℤₘ₀ := valued.mk' (power_series.ideal_X K).valuation

section complete

open_locale filter

def coeff_map (d : ℤ) : laurent_series K → K := λ x, x.coeff d

lemma uniform_continuous_coeff_map {uK : uniform_space K} (h : uniformity K = 𝓟 id_rel) (d : ℤ) :
  uniform_continuous (coeff_map K d) := sorry

/- The definition below avoids the assumption that `K` be endowed with the trivial uniformity,
  rather putting this in the proof.
-/
open filter topological_space
open_locale filter topology uniformity

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

lemma cauchy.bot₁ {ℱ : filter (laurent_series K)} (hℱ : cauchy ℱ) : ∃ N, 
  ∀ᶠ y in ℱ, ∀ n ≤ N, coeff_map K n y = (0 : K) :=
begin
  sorry,
  -- obtain ⟨S, ⟨hS, ⟨T, ⟨hT, H⟩⟩⟩⟩ := filter.mem_prod_iff.mp (filter.le_def.mp hℱ.2 (entourage K 0)
  --   (entourage_uniformity_mem _ _)),
  -- obtain ⟨x, hx⟩ := filter.forall_mem_nonempty_iff_ne_bot.mpr hℱ.1 (S ∩ T)
  --   (by {exact inter_mem_iff.mpr ⟨hS, hT⟩}),
  -- obtain ⟨N, hN⟩ := bounded_supp_of_mem_entourage x 0,
  -- use N,
  -- rw filter.eventually,
  -- apply mem_of_superset (inter_mem hS hT),
  -- suffices : (S ∩ T) ×ˢ (S ∩ T) ⊆ entourage K 0,
  -- { intros y hy,
  --   have h_prod : (x, y) ∈ entourage K 0,
  --   { refine this (mem_prod.mpr _),
  --     exact ⟨hx, hy⟩ },
  --   exact hN y h_prod },
  -- exact (prod_mono (inter_subset_left S T) (inter_subset_right S T)).trans H,
end

lemma cauchy.bot_aux {ℱ : filter (laurent_series K)} (hℱ : cauchy ℱ) : ∃ N, 
  ∀ n ≤ N, ℱ.map (coeff_map K n) ≤ filter.principal {0} :=
begin
  simp only [principal_singleton, pure_zero, nonpos_iff, mem_map],
  obtain ⟨N, hN⟩ := hℱ.bot₁,
  use  N,
  intros n hn,
  apply filter.mem_of_superset hN,
  intros a ha,
  exact ha n hn,
end

-- lemma cauchy.coeff_map_zero_at_bot' {ℱ : filter (ratfunc K)} (hℱ : cauchy ℱ) : ∀ᶠ n in at_bot,
--   ℱ.map (ratfunc.coeff_map K n) ≤ filter.principal {0} :=
-- eventually_at_bot.mpr (cauchy.coeff_map_zero_at_bot hℱ)

lemma cauchy.bot₂ {ℱ : filter (laurent_series K)} (hℱ : cauchy ℱ) : ∃ N, ∀ n,
  n ≤ N → (hℱ.coeff_map' n) = 0 :=
begin
  letI : uniform_space K := ⊥,
  have hK : uniformity K = filter.principal id_rel, refl,
  obtain ⟨N, hN⟩ := hℱ.bot_aux,
  use N,
  intros n hn,
  exact ne_bot_unique_principal hK (hℱ.map (uniform_continuous_coeff_map K hK n)).1
    (aux_coeff_map' _ _) (hN n hn),
end

lemma cauchy.bot₃ {ℱ : filter (laurent_series K)} (hℱ : cauchy ℱ) :
  ∀ᶠ f in ℱ, ∀ d ≤ linear_order.min hℱ.bot₁.some hℱ.bot₂.some, 
  coeff_map K d f = (hℱ.coeff_map' d) :=
begin
  have hN := hℱ.bot₁.some_spec,
  set N := hℱ.bot₁.some with hN₀,
  rw ← hN₀ at hN,
  have hM := hℱ.bot₂.some_spec,
  set M := hℱ.bot₂.some with hM₀,
  rw ← hM₀ at hM,
  apply ℱ.3 hN (λ a ha, _),
  intros d hd,
  rw [ha d (le_trans hd (min_le_left _ _)), hM d (le_trans hd (min_le_right _ _))],
end

lemma cauchy.coeff_map_support_bdd'' {ℱ : filter (laurent_series K)} (hℱ : cauchy ℱ) :
  bdd_below (hℱ.coeff_map'.support) :=
begin
  refine ⟨hℱ.bot₂.some, λ d hd, _⟩,
  by_contra' hNd,
  exact hd (hℱ.bot₂.some_spec d (le_of_lt hNd)),
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

lemma cauchy.eventually₁ {ℱ : filter (laurent_series K)} (hℱ : cauchy ℱ) :
∀ D : ℤ, ∀ᶠ f in ℱ, ∀ d, d ≤ D → (hℱ.coeff_map' d) = coeff_map K d f := 
begin
  intro D,
  set X : ℤ → set (laurent_series K) := λ d, {f | (hℱ.coeff_map' d) = coeff_map K d f} with hX,
  have intersec : (⋂ d, X d) ⊆ {x : laurent_series K | ∀ (d : ℤ), d ≤ D → hℱ.coeff_map' d = coeff_map K d x},
  -- have intersec : ({d : ℤ | d ≤ D}.Inter, (X d.1) ⊆ 
    -- {x : laurent_series K | ∀ (d : ℤ), d ≤ D → hℱ.coeff_map' d = coeff_map K d x},
    
  -- { ext f,
  --   split,
  --   { intros hf S hS,
  --     simp only [set.mem_set_of_eq] at hf,
  --     simp only [set.mem_range, hX] at hS,
  --     obtain ⟨s, hs⟩ := hS,
  --     rw ← hs,
  --     simp,
  --     apply hf,
  --     sorry,},
    { intros f hf n hn,
      simp only [set.mem_Inter, set.mem_set_of_eq, hX] at hf,
      exact hf n },
  suffices : (⋂ d, X d) ∈ ℱ,
  exact ℱ.3 this intersec,
  -- rw filter.eventually_iff,
  -- rw hX at this,
    -- simp_rw [← hf₃],
  -- { ext f,
  -- },
  
  -- convert this,
  -- simp,
  -- apply this,

  
  set N := linear_order.min hℱ.bot₁.some hℱ.bot₂.some with hN₀,
  by_cases H : D ≤ N,--forse non serve, il finset.Ico N D e' vuoto ed e' ok
  -- sorry,
  { have := @filter.bInter_mem (laurent_series K) ℱ (finset.Ico N D) _ (set.univ) _,



  },
  -- -- suffices uno : ∀ᶠ f in ℱ, ∀ d, coeff_map K d f = (hℱ.coeff_map' d),
  -- -- { apply filter.eventually.mono uno,
  -- --   simp,
  -- --   intros f H d hDd,
  -- --   exact (H d).symm },
  -- have sopra := aux_coeff_map' hℱ,
  -- -- simp_rw [← principal_singleton],
  -- simp_rw [principal_singleton, tendsto_pure] at sopra,
  -- apply eventually.mono,
  -- intros f hf d hdD,
  -- suffices nuova_tesi : ∀ᶠ (f : laurent_series K) in ℱ, ∀ᶠ d in at_bot, coeff_map K d f =
  --   cauchy.coeff_map' hℱ d,--se bastasse, potrei usare questa invece della tesi attuale
  -- sorry,
  -- have sopra := aux_coeff_map' hℱ,
  -- simp_rw [principal_singleton, tendsto_pure] at sopra,
  -- replace sopra := @eventually_of_forall ℤ _ at_bot sopra,
  -- convert sopra,
  -- simp,
  -- split,
  -- { intro H,
  --   obtain ⟨f, ⟨m, hm⟩⟩ := @eventually.exists _ _ ℱ hℱ.1 H,
  --   use m,
  --   intros b hb,
  --   specialize hm b hb,
  --   -- apply H.mono,
  --   -- rintros g ⟨k, hk⟩,
    

  -- },
  -- congr,
  -- congr,
  -- simp_rw eventually_at_bot,
  -- apply filter.eventually.mono,

  
  -- have := @eventually_eventually_nhds,
  -- simp at sopra,

  -- intros D,
  
  
  -- specialize this D,
  -- suffices nuova_tesi : ∀ᶠ d in at_bot, ∀ᶠ (f : laurent_series K) in ℱ, cauchy.coeff_map' hℱ d =
  --   coeff_map K d f,
  -- -- simp_rw eventually_at_bot at nuova_tesi,
  -- -- obtain ⟨D₁, hD₁⟩ := nuova_tesi,
  -- -- apply nuova_tesi,
  -- -- apply filter.eventually.mono,
  -- have ff := filter.forall_eventually_of_eventually_forall,
  -- refine eventually_top.mpr _ ℱ.sets,
  -- apply forall_eventually_of_eventually_forall,
  -- apply this,
  -- -- simp_rw [← tendsto_pure] at this,
  -- -- suffices non_basta_ma_inizio : ∀ᶠ f in ℱ, coeff_map K D f = (hℱ.coeff_map' D),
  -- -- sorry,
  -- rw [← tendsto_pure, ← principal_singleton] at this,
  -- apply aux_coeff_map',
end

lemma diff.eventually₀ {f g : (laurent_series K)} {D : ℤ}
  (H : ∀ d, d ≤ D → coeff_map K d g = coeff_map K d f) :
  valued.v (f - g) < ↑(multiplicative.of_add D) := sorry

lemma cauchy.eventually₂ {ℱ : filter (laurent_series K)} (hℱ : cauchy ℱ)
  {U : set (laurent_series K)} (hU : U ∈ 𝓝 (hℱ.mk_laurent_series)) : ∀ᶠ f in ℱ, f ∈ U := 
begin
  rw valued.mem_nhds at hU,
  obtain ⟨γ, hU₁⟩ := hU,
  suffices : ∀ᶠ f in ℱ, f ∈ {y : laurent_series K | valued.v (y - hℱ.mk_laurent_series) < ↑γ},
  apply this.mono (λ _ hf, hU₁ hf),
  have pigrizia : ∃ D : ℤ, ((multiplicative.of_add D) : ℤₘ₀)= γ,sorry,
  obtain ⟨D, hD⟩ := pigrizia,
  apply (hℱ.eventually₁ D).mono,
  intros f hf,
  rw [set.mem_set_of_eq, ← hD],
  apply (diff.eventually₀),
  apply hf,
  -- have sopra := aux_coeff_map' hℱ D,
  -- -- have qui := hℱ.eventually₁ D,
  -- simp only [principal_singleton, tendsto_pure] at sopra,
  -- apply filter.eventually.mono sopra,
  -- intros f hf,
  -- simp only [set.mem_set_of_eq],
  -- -- apply (diff.eventually₀),
  -- -- apply hf,
end

-- def new.entourage (d : ℕ) : set (laurent_series K × laurent_series K) :=
--   {P | (power_series.ideal_X K).valuation (P.1 - P.2) < ↑(multiplicative.of_add (- (d : ℤ)))}

-- lemma new.entourage_uniformity_mem (d : ℕ) : new.entourage d ∈ 𝓤 (laurent_series K) := sorry

-- example : normed_field (laurent_series K) := 

instance : complete_space (laurent_series K) :=
begin
  -- have := cau_seq.is_complete (laurent_series K) norm,
  -- apply complete_space_of_cau_seq_complete,
  -- haveI : (uniformity (laurent_series K)).is_countably_generated, sorry,
  -- apply uniform_space.complete_of_cauchy_seq_tendsto,
  -- intros u hu,
  -- rw cauchy_seq at hu,
  -- rcases hu with ⟨h1, h2⟩,
  -- simp at hu,
  fconstructor,
  rintros ℱ hℱ,
  -- let HF := hℱ,
  use hℱ.mk_laurent_series,
  -- have subtest : (𝓝 (hℱ.mk_laurent_series) ×ᶠ 𝓝 (hℱ.mk_laurent_series)) ≤ 𝓤 (laurent_series K),
  -- sorry,
  -- -- have subtest : (𝓝 (hℱ.mk_laurent_series) ×ˢ 𝓝 (hℱ.mk_laurent_series)) ∈ 𝓤 (laurent_series K),
  -- -- sorry,
  -- rcases hℱ with ⟨h₁, h₂⟩,
  -- rw [filter.le_def] at h₂,
  rw filter.le_def,
  intros S hS,
  exact hℱ.eventually₂ hS,
  

  -- rw filter.eventually_mem
  -- rw valued.
  -- obtain ⟨V, ⟨hV, hV_S⟩⟩ := uniform_space.mem_nhds_iff.mp hS,
  -- apply ℱ.3 _ hV_S,
  -- simp,
  -- rw uniform_space.ball at hV_S ⊢,
  -- specialize h₂ V hV,
  -- rw filter.mem_prod_iff at h₂,
  -- obtain ⟨T₁, hT₁, T₂, hT₂, H⟩ := h₂,
  -- set T := T₁ ∩ T₂ with hT,
  -- have := ℱ.4 hT₁ hT₂,
  -- rw [← hT] at this,
  -- have uff : T ⊆ prod.mk (cauchy.mk_laurent_series _) ⁻¹' V,
  -- { have sette : T ×ˢ T ⊆ V,
  --   apply _root_.subset_trans _ H,
  --   sorry,--this is really easy
  --   --refine principal_le_iff.mp _ (prod.mk (cauchy.mk_laurent_series _) ⁻¹' V) _,

  -- },
  -- apply ℱ.3 _ uff,
  -- exact this,
  -- -- rw [← filter.prod_comap_comap_eq],
  -- -- simp at this,
  -- -- simp,
  -- -- refine set.mem_Inter.mp _ (ball (cauchy.mk_laurent_series ⟨h₁, h₂⟩) V),
  -- -- simp,
  -- -- intro X,
  
  -- -- obtain ⟨T, ⟨hT, hT_S⟩⟩ := _root_.mem_nhds_iff.mp hS,



  -- have test : S ×ˢ S ∈ 𝓤 (laurent_series K),
  -- { have uno := filter.prod_mem_prod hS hS,
  --   have due : is_open S, sorry,
  --   rw [uniform_space.is_open_uniformity] at due,
  --   have easy : cauchy.mk_laurent_series HF ∈ S, sorry,
  --   specialize due (HF.mk_laurent_series) easy,
  --   convert due,
  --   -- simp,

  --   -- sorry,--easy

  --   -- use uno,
  --   -- rw filter.le_def at subtest,
  --   -- specialize subtest S
    
  -- },
  -- specialize h₂ (S ×ˢ S) test,
  -- rw filter.mem_prod_self_iff at h₂,
  -- obtain ⟨T, ⟨a, b⟩⟩ := h₂,
  -- rw set.prod_self_subset_prod_self at b,
  -- refine ℱ.3 _ b,
  -- simp,
  -- exact a,

  

  -- obtain ⟨V, H, hV⟩ := hℱ.eventually₁.exists_mem,

  -- apply sequentially_complete.le_nhds_of_seq_tendsto_nhds hℱ (new.entourage_uniformity_mem),
  -- { intros S hS,
  --   rw uniformity_eq_comap_nhds_zero at hS,
  --   simp at hS,
  --   sorry,
  -- },
  -- { have uno := hℱ.eventually₁,
  --   simp_rw [eventually_at_bot, eventually_iff] at uno,


  --   rw tendsto_at_top',
  --   intros S hS,
  --   rw valued.mem_nhds at hS,
  --   obtain ⟨n_mul, hn_mul⟩ := hS,
  --   obtain ⟨n, hn⟩ : ∃ n : ℕ, (multiplicative.of_add (n : ℤ) : ℤₘ₀) = n_mul, sorry,--sono pigro
  --   use n,
  --   intros d hd,
  --   apply hn_mul,
  --   simp only [set.mem_set_of_eq],
  --   -- rw sequentially_complete.seq,
  --   suffices : sequentially_complete.seq hℱ new.entourage_uniformity_mem d -
  --     cauchy.mk_laurent_series hℱ = 0,
  --   {rw this, simp },
    
    

  -- },
  -- -- rw filter.le_def,
  -- -- intros S hS,
  -- -- replace hS := uniform_space.mem_nhds_iff.mp hS,
  -- -- rw uniformity_eq_comap_nhds_zero at hS,
  -- -- obtain ⟨V, hV, hV_S⟩ := hS,
  -- -- simp only [mem_comap, exists_prop] at hV,
  -- -- obtain ⟨U, hU, hU_S⟩ := hV,
  -- -- have H := hℱ.eventually₁,
  -- -- simp_rw [eventually_at_bot, eventually_iff] at H,
  -- -- have mah : U = {x : laurent_series K | ∃ (a : ℤ), ∀ (b : ℤ), b ≤ a → cauchy.coeff_map' hℱ b =
  -- --   coeff_map K b x}, sorry,
  -- -- -- rw ← mah at H,
  -- -- refine ℱ.3 _ hV_S,
  -- -- refine ℱ.3 _ (ball_mono hU_S (cauchy.mk_laurent_series hℱ)),
  -- -- rw mah,
  -- -- simp only [set.preimage_set_of_eq, filter.mem_sets],
  
end

end complete

lemma coe_range_dense : dense_range (coe : (ratfunc K) → (laurent_series K)) := sorry

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

end completion_laurent_series