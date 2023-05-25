import for_mathlib.laurent_series_iso.power_series_adic_completion
import topology.uniform_space.abstract_completion

noncomputable theory

variables (K : Type*) [field K]

open uniform_space ratfunc

instance : uniform_space (laurent_series K) := sorry

instance : separated_space (laurent_series K) := sorry

instance : complete_space (laurent_series K) := sorry

instance : topological_ring (laurent_series K) := sorry

instance : uniform_add_group (laurent_series K) := sorry

noncomputable!
def coe_is_inducing : uniform_inducing (coe : (ratfunc K) → (laurent_series K)) :=
{ comap_uniformity := sorry }

lemma unif_cont_coe : uniform_continuous (coe : (ratfunc K) → (laurent_series K)) := sorry

noncomputable!
def coe_hom : (ratfunc K) →+* (laurent_series K) :=
{ to_fun := coe,
  map_one' := sorry,
  map_mul' := sorry,
  map_zero' := sorry,
  map_add' := sorry }

lemma coe_hom_cont : continuous (coe_hom K) := sorry

def ϕ := uniform_space.completion.extension_hom (coe_hom K)

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
  abstract_completion.compare_equiv (ratfunc_pkg K) (laurent_series_pkg K)

lemma unif_cnt_ψ : uniform_continuous (ψ K) := sorry

lemma aux (f : ratfunc K) : (f : laurent_series K) = ψ K ↑f := sorry

lemma ϕ_eq_ψ : (ϕ K (coe_hom_cont K)).to_fun = (ψ K).to_fun :=
  uniform_space.completion.extension_unique (unif_cont_coe K) (unif_cnt_ψ K) (aux K)

noncomputable! def laurent_series.ring_equiv' : 
  ring_equiv (completion_of_ratfunc K) (laurent_series K) :=
{ map_mul' := (ϕ K (coe_hom_cont K)).map_mul',
  map_add' := (ϕ K (coe_hom_cont K)).map_add',
  .. ψ K }