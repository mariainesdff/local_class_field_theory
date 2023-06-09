import topology.uniform_space.completion

variables (X : Type*) [uniform_space X] 
variables (K : set X) [hK : is_closed K]
variables (K' : set (uniform_space.completion X)) --[hK' : is_closed K']

open_locale big_operators

-- example : uniform_space K := infer_instance
-- noncomputable
def inter_as_set : set K' := λ x, (coe '' K : (set (uniform_space.completion X))) x
-- def bleah : set K' := λ x, (coe '' K : (set (uniform_space.completion X))) x
-- def bleah (h_sub : coe '' K ⊆ K') : set K' := λ x, (coe '' K : (set (uniform_space.completion X))) x

--#check inter_as_set X K K'

lemma completion_closed_inter_univ (h_sub : coe '' K ⊆ K')
  (H : dense (inter_as_set X  K K')) : K' ∩ (coe '' (set.univ : set X)) = coe '' K :=
begin
  set Y := {x : uniform_space.completion X // x ∈ K' ∩ (coe '' (set.univ : set X))} with hY,
  haveI : uniform_space Y := infer_instance,
  set K'' : set Y :=  {x : Y | ∃ (y : K), (y : uniform_space.completion X) = ↑x } with hK'',
  --set K'' : set Y := λ x, ((coe '' K : (set (uniform_space.completion X))) x) with hK'',
  have h_closed : is_closed K'', 
  { sorry },
  replace h_closed := is_closed.closure_eq h_closed,
  have h_dense : dense K'', 
  { sorry },
  rw h_dense.closure_eq at h_closed,
  have h1 : (coe '' K'' : set (uniform_space.completion X)) = (coe '' K),
  { ext x', 
    simp only [set.mem_image, set.mem_set_of_eq, coe_coe, set_coe.exists, subtype.coe_mk, 
      exists_prop, subtype.exists, set.mem_inter_iff, set.mem_univ, true_and,
      exists_eq_right_right, and_iff_right_iff_imp, forall_exists_index, and_imp],
    intros x hx hcoe,
    refine ⟨_, ⟨x, hcoe⟩⟩,
    { apply h_sub,
      rw [← hcoe, set.mem_image],
      exact ⟨x, hx, rfl⟩ }},
  have h2 : (coe '' (set.univ : set Y) : set (uniform_space.completion X)) = 
    K' ∩ coe '' (set.univ : set X),
  { ext x',
    simp only [set.image_univ, subtype.range_coe_subtype, set.mem_set_of_eq],},
  simp only [← h1, ← h2, h_closed], 

end
  -- (uniform_space.completion K) := sorry
  
  -- (set (uniform_space.completion X))) : true :=