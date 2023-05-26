import for_mathlib.laurent_series_iso.power_series_adic_completion
import topology.uniform_space.abstract_completion

noncomputable theory

variables (K : Type*) [field K]

open uniform_space ratfunc power_series abstract_completion
open_locale discrete_valuation

namespace completion_laurent_series

def ideal_X : is_dedekind_domain.height_one_spectrum (power_series K) := 
{ as_ideal := ideal.span({X}),
  is_prime := power_series.span_X_is_prime,
  ne_bot   := by { rw [ne.def, ideal.span_singleton_eq_bot], exact X_ne_zero }} 

instance : valued (laurent_series K) ℤₘ₀ := valued.mk' (ideal_X K).valuation

instance : complete_space (laurent_series K) := sorry

noncomputable!
def coe_is_inducing : uniform_inducing (coe : (ratfunc K) → (laurent_series K)) :=
{ comap_uniformity := sorry }

lemma unif_cont_coe : uniform_continuous (coe : (ratfunc K) → (laurent_series K)) := sorry

lemma coe_hom_cont : continuous (coe_alg_hom K) := sorry

def ϕ := uniform_space.completion.extension_hom (coe_alg_hom K).to_ring_hom

lemma coe_range_dense : dense_range (coe : (ratfunc K) → (laurent_series K)) := sorry

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

def ψ : (completion_of_ratfunc K) ≃ᵤ laurent_series K :=
  compare_equiv (ratfunc_pkg K) (laurent_series_pkg K)

lemma aux (f : ratfunc K) : (f : laurent_series K) = ψ K ↑f :=
begin
  classical,
  dsimp [ψ, ϕ, ratfunc_pkg, laurent_series_pkg, compare_equiv, compare,
    abstract_completion.extend],
  rw [if_pos (unif_cont_coe K)],
  sorry,
end

lemma ϕ_eq_ψ : (ϕ K (coe_hom_cont K)).to_fun = (ψ K).to_fun :=
  uniform_space.completion.extension_unique (unif_cont_coe K)
    (uniform_continuous_compare_equiv _ _) (aux K)

noncomputable! def  laurent_series_ring_equiv' : 
  ring_equiv (completion_of_ratfunc K) (laurent_series K) :=
{ map_mul' := (ϕ K (coe_hom_cont K)).map_mul',
  map_add' := (ϕ K (coe_hom_cont K)).map_add',
  .. ψ K }

end completion_laurent_series