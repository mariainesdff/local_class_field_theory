import for_mathlib.power_series_adic_completion
import topology.uniform_space.abstract_completion

noncomputable theory

variables (K : Type*) [field K]

open uniform_space ratfunc

instance : uniform_space (laurent_series K) := sorry

instance : separated_space (laurent_series K) := sorry

instance : complete_space (laurent_series K) := sorry

noncomputable!
def coe_is_inducing : uniform_inducing (coe : (ratfunc K) → (laurent_series K)) :=
{ comap_uniformity := sorry }

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

-- noncomputable!
def ψ : (completion_of_ratfunc K) ≃ᵤ laurent_series K :=
  abstract_completion.compare_equiv (ratfunc_pkg K) (laurent_series_pkg K)

-- def ϕ : (completion_of_ratfunc K) → laurent_series K :=
#check uniform_space.completion.extension (coe : (ratfunc K) → (laurent_series K))

section sub

lemma has_sub_hat : @has_neg.neg (completion_of_ratfunc K) _ =
  uniform_space.completion.map (@has_neg.neg (ratfunc K) _) :=
begin
  sorry,
end

lemma at_least_for_neg (f : completion_of_ratfunc K) : (ψ K) (-f) = - (ψ K) f :=
begin
  suffices : (ψ K) ∘ has_neg.neg = has_neg.neg ∘ (ψ K),
  exact congr_fun this f,
  rw has_sub_hat,
  rw ψ,
  sorry,
end


end sub

