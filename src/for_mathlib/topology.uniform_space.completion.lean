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
  set Y := K' ∩ (coe '' (set.univ : set X)) with hY,
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
    simp only [set.image_univ, subtype.range_coe_subtype, set.mem_inter_iff, set.mem_set_of_eq] },
  simp only [hY,← h1, ← h2, h_closed], 
end


local notation `φ` := (coe : X → uniform_space.completion X)

lemma dense_inducing_comp (A B C : Type*) [topological_space A] [topological_space B] [topological_space C]
 (f : A → B) (g : B → C) (h : dense_inducing f) (h': dense_inducing g) : dense_inducing (g ∘ f) :=
begin
  refine {to_inducing := _, dense := _},
  refine inducing.comp h'.1 h.1,
  refine dense_range.comp h'.dense h.dense _,
  refine dense_inducing.continuous h',
end

/-**USEFUL LEMMAS**
* uniform_embedding.dense_embedding
* dense_embedding.subtype
-/
lemma foo (h_incl : set.maps_to φ K K' ) (h_triv : set.maps_to φ K (φ '' set.univ))
  (h1 : dense_embedding (set.maps_to.restrict _ _ _ h_incl)) 
  (h2 : closed_embedding (set.maps_to.restrict _ _ _ h_triv)) 
  : φ '' K = K' ∩ (φ '' set.univ) :=
begin
  set S := K' ∩ (φ '' set.univ) with hS,
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

  -- have uno := dense.closure_eq,
  -- have := h1.1,
  have one := ((dense_embedding.dense_image h1S).mpr (dense_univ)).closure_eq,
  have two := (closed_embedding.closed_iff_image_closed h2S).mp (is_closed_univ),
  rw two.closure_eq at one,
end
