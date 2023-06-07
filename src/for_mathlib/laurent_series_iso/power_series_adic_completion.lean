import for_mathlib.laurent_series_iso.old_power_series_adic_completion
import topology.uniform_space.abstract_completion

noncomputable theory

open uniform_space ratfunc power_series abstract_completion is_dedekind_domain.height_one_spectrum polynomial
open_locale discrete_valuation

-- namespace laurent_series

-- /-The main point of this section is to prove the equality between the X-adic valuation and the order of laurent_series. Applying then `fae_order_eq_val'`, we deduce that for every `f : ratfunc`, the equality of `f : ratfunc` coincides with the valuation of `↑f : laurent_series` -/



-- end laurent_series

namespace completion_laurent_series

variables (K : Type*) [field K]

def power_series.ideal_X (K : Type*) [field K] : is_dedekind_domain.height_one_spectrum (power_series K) := 
{ as_ideal := ideal.span({X}),
  is_prime := power_series.span_X_is_prime,
  ne_bot   := by { rw [ne.def, ideal.span_singleton_eq_bot], exact X_ne_zero }} 

instance : valued (laurent_series K) ℤₘ₀ := valued.mk' (power_series.ideal_X K).valuation

instance : complete_space (laurent_series K) := sorry

lemma coe_range_dense : dense_range (coe : (ratfunc K) → (laurent_series K)) := sorry

local attribute [instance] classical.prop_decidable
open multiplicity unique_factorization_monoid

lemma aux_old_pol (P : (polynomial K)) : 
  multiset.count (power_series.ideal_X K).as_ideal (normalized_factors (ideal.span {↑P})) =
  multiset.count (ideal.span {polynomial.X} : ideal (polynomial K)) (normalized_factors (ideal.span {P})) :=
begin
  sorry,
end




lemma should_be_in_old_pol (P : (polynomial K)) : (ideal_X K).int_valuation (P) =
  (power_series.ideal_X K).int_valuation (↑P : (power_series K)) :=
begin
  by_cases hP : P = 0,
  sorry,
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
    rw ← aux_old_pol,
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
  have := @valuation_of_mk' (power_series K) _ _ _ (laurent_series K) _ _ _ (power_series.ideal_X K) ↑f ⟨g, mem_non_zero_divisors_iff_ne_zero.2 $ coe_ne_zero h⟩,
  convert this;
  apply should_be_in_old_pol,
end


lemma should_be_in_old (P₁ P₂ : (ratfunc K)) : valued.v (P₁ - P₂) = valued.v ((↑P₁ : (laurent_series K)) - ↑P₂) :=
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

noncomputable! def  laurent_series_ring_equiv' : 
  ring_equiv (completion_of_ratfunc K) (laurent_series K) :=
{ map_mul' := (extension_as_ring_hom K (unif_cont_coe K).continuous).map_mul',
  map_add' := (extension_as_ring_hom K (unif_cont_coe K).continuous).map_add',
  .. compare_pkg K }

end completion_laurent_series