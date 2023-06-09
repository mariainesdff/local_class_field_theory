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

#check inter_as_set X K K'

lemma completion_closed_inter_univ (h_sub : coe '' K ⊆ K')
  (H : dense (inter_as_set X  K K')) : K' ∩ (coe '' (set.univ : set X)) = coe '' K :=
begin
  have h_closed : is_closed (inter_as_set X  K K'), sorry,
  replace h_closed := is_closed.closure_eq h_closed,
  rw H.closure_eq at h_closed,

end
  -- (uniform_space.completion K) := sorry
  
  -- (set (uniform_space.completion X))) : true :=