import topology.uniform_space.abstract_completion

/-! 
# Abstract completion
Let `f : α → β` be a continuous function between a uniform space `α` and a regular topological 
space `β`, and let `pkg, pkg'` be two abstract completions of `α`. The main result is that 
if for every point `a : pkg` the filter `f.map (coe⁻¹ (𝓝 a))` obtained by pushing forward with `f`
the preimage in `α` of `𝓝 a` tends to `𝓝 (f.extend a : β)`, then the comparison map
between `pkg` and `pkg'` composed with the extension of `f` to `pkg`` coincides with the
extension of `f` to `pkg'` -/

namespace abstract_completion

open_locale topology

variables {α β : Type*} [uniform_space α] [topological_space β]
variables (pkg : abstract_completion α) (pkg' : abstract_completion α) 

/-- The topological space underlying a uniform space -/
definition top_pkg : topological_space pkg.space := pkg.uniform_struct.to_topological_space

local attribute [instance] top_pkg

include pkg pkg'

lemma extend_compare_extend [t3_space β] (f : α → β) (cont_f : continuous f) 
  (hf : ∀ a : pkg.space, filter.tendsto f (filter.comap pkg.coe (𝓝 a))
    (𝓝 ((pkg.dense_inducing.extend f) a))) :
    (pkg.dense_inducing.extend f) ∘ (pkg'.compare pkg) = (pkg'.dense_inducing.extend f) :=
begin
  have : ∀ (x : α), (((pkg.dense_inducing.extend f)) ∘ pkg'.compare pkg) (pkg'.coe x) = f x,
  { intro a,
    rw [function.comp_app, compare_coe],
    apply dense_inducing.extend_eq _ cont_f },
  refine (dense_inducing.extend_unique (abstract_completion.dense_inducing _) this _).symm,
  letI := pkg'.uniform_struct,
  letI := pkg.uniform_struct,
  refine continuous.comp _ (uniform_continuous_compare pkg' pkg).continuous,
  apply dense_inducing.continuous_extend,
  use λ a, ⟨(pkg.dense_inducing.extend f) a, hf a⟩,
end

end abstract_completion

#lint