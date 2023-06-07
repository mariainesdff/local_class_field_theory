import for_mathlib.laurent_series_iso.old_power_series_adic_completion
import topology.uniform_space.abstract_completion

noncomputable theory

open uniform_space ratfunc power_series abstract_completion
open_locale discrete_valuation

namespace completion_laurent_series

variables (K : Type*) [field K]

def ideal_X (K : Type*) [field K] : is_dedekind_domain.height_one_spectrum (power_series K) := 
{ as_ideal := ideal.span({X}),
  is_prime := power_series.span_X_is_prime,
  ne_bot   := by { rw [ne.def, ideal.span_singleton_eq_bot], exact X_ne_zero }} 

instance : valued (laurent_series K) ℤₘ₀ := valued.mk' (ideal_X K).valuation

instance : complete_space (laurent_series K) := sorry

lemma coe_range_dense : dense_range (coe : (ratfunc K) → (laurent_series K)) := sorry

noncomputable!
def coe_is_inducing : uniform_inducing (coe : (ratfunc K) → (laurent_series K)) :=
{ comap_uniformity := sorry }

lemma coe_is_inducing' : uniform_inducing (coe : (ratfunc K) → (laurent_series K)) :=
begin
  rw uniform_inducing_iff,
  rw filter.comap,
  ext S,
  split,
  { intro hS,
    simp at hS,
    obtain ⟨T, ⟨hT, pre_T⟩⟩ := hS,
    rw uniformity_eq_comap_nhds_zero at hT ⊢,
    simp at hT ⊢,
    obtain ⟨R, ⟨hR, pre_R⟩⟩ := hT,
    obtain ⟨d, hd⟩ := valued.mem_nhds.mp hR,
    simp only [sub_zero] at hd,--useless?

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
      simp only [set.mem_set_of_eq],
      sorry,--this is the statement that 

    },
    -- let := (λ (x : laurent_series K × laurent_series K), x.snd - x.fst),
    -- rw uniformi
    -- simp at pre_T,

  },
  -- simp,
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