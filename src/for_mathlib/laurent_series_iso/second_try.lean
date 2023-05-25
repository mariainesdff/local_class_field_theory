import for_mathlib.laurent_series_iso.power_series_adic_completion
import topology.uniform_space.abstract_completion

noncomputable theory

variables (K : Type*) [field K]

open uniform_space

-- instance : uniform_space (laurent_series K) := sorry

-- instance : complete_space (laurent_series K) := sorry

-- example : uniform_space (ratfunc K) := infer_instance

noncomputable def laurent_series_as_pkg : abstract_completion (ratfunc K) :=
begin
  sorry,
end

-- def φ : (ratfunc K) → (laurent_series K) := sorry

-- lemma uniform_continuous_φ : uniform_continuous (φ K):= sorry

-- def ψ₀ := uniform_space.completion.extension (φ K)

-- def ψ : (completion_of_ratfunc K) ≃ laurent_series K :=
-- -- def ψ : (completion_of_ratfunc K) ≃ᵤ laurent_series K :=
-- begin
--   have : 0 = 0,
-- end 
