import topology.uniform_space.completion

variables (X : Type*) [uniform_space X] 
variables (K : set X) [hK : is_closed K]
variables (K' : set (uniform_space.completion X)) --[hK' : is_closed K']

open_locale big_operators

-- noncomputable
def inter_as_set : set K' := λ x, (coe '' K : (set (uniform_space.completion X))) x
-- def bleah : set K' := λ x, (coe '' K : (set (uniform_space.completion X))) x
-- def bleah (h_sub : coe '' K ⊆ K') : set K' := λ x, (coe '' K : (set (uniform_space.completion X))) x

--#check inter_as_set X K K'

lemma completion_closed_inter_univ (h_sub : coe '' K ⊆ K')
  (H : dense (inter_as_set X  K K')) : K' ∩ (coe '' (set.univ : set X)) = coe '' K :=
begin
  set S := K' ∩ (coe '' (set.univ : set X)) with hS,
  haveI : uniform_space S := infer_instance,
  set K'' : set S :=  {x : S | ∃ (y : K), (y : uniform_space.completion X) = ↑x } with hK'',
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
  have h2 : (coe '' (set.univ : set S) : set (uniform_space.completion X)) = 
    K' ∩ coe '' (set.univ : set X),
  { ext x',
    simp only [set.image_univ, subtype.range_coe_subtype, set.mem_inter_iff, set.mem_set_of_eq] },
  simp only [hS,← h1, ← h2, h_closed], 
end


local notation `φ` := (coe : X → uniform_space.completion X)

lemma dense_of

lemma dense_inducing_of_inducing_comp (A B : Type*) [topological_space A] [topological_space B] 
  {f : A → B} (h : dense_inducing f) (S : set B) (H : ∀ a : A, f a ∈ S)
    : dense_inducing (set.cod_restrict f S H) :=  
begin
  refine {to_inducing := _, dense := _},
  apply inducing.cod_restrict h.1,
  rw dense_range_iff_closure_range,
  have := dense_inducing.closure_range h,
  sorry,  
  -- have :=
end

/-**USEFUL LEMMAS**
* uniform_embedding.dense_embedding
* dense_embedding.subtype
-/
lemma foo (h_incl : set.maps_to φ K K' ) (h_triv : set.maps_to φ K (φ '' set.univ))
  (H1 : dense_embedding (set.maps_to.restrict _ _ _ h_incl)) 
  (H2 : closed_embedding (set.maps_to.restrict _ _ _ h_triv)) 
  : φ '' K = K' ∩ (φ '' set.univ) :=
begin
  have h_sub : coe '' K ⊆ K', sorry,
  set S := K' ∩ (φ '' set.univ) with hS,
  set K'' : set S :=  {x : S | ∃ (y : K), (y : uniform_space.completion X) = ↑x } with hK'',
  have h_inclS : set.maps_to φ K S, sorry,
  -- let ι₁: S → K' := λ x, inter_mem,
  -- { apply set.maps_to.comp,

  -- },
  have h1S : dense_embedding (set.maps_to.restrict _ _ _ h_inclS),
  { have := @dense.dense_embedding_coe,    
    sorry, --apply dense_inducing_comp,
    -- apply dense_inducing.mk,
    -- sorry,
  },
  have h2S : closed_embedding (set.maps_to.restrict _ _ _ h_inclS),
  { sorry,

  },

  -- From here on, it is María Inés' proof:
  have h_closed : is_closed K'', 
  { sorry },--hopefully follows, or can be replaced,by h2S
  replace h_closed := is_closed.closure_eq h_closed,
  have h_dense : dense K'', 
  { sorry },--hopefully follows, or can be replaced,by h1S
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
  have h2 : (coe '' (set.univ : set S) : set (uniform_space.completion X)) = 
    K' ∩ coe '' (set.univ : set X),
  { ext x',
    simp only [set.image_univ, subtype.range_coe_subtype, set.mem_inter_iff, set.mem_set_of_eq] },
  simp only [hS,← h1, ← h2, h_closed], 
end
