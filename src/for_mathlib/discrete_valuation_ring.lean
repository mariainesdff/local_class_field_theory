import discrete_valuation_ring.basic

theorem ring_equiv.discrete_valuation_ring {A  B : Type*} [comm_ring A] [is_domain A]
  [discrete_valuation_ring A] [comm_ring B] [is_domain B] (e : A ≃+* B) :
  discrete_valuation_ring B :=
{ to_is_principal_ideal_ring := is_principal_ideal_ring.of_surjective e.to_ring_hom e.surjective,
  to_local_ring  := e.local_ring,
  not_a_field'   := 
  begin
    have hA : local_ring.maximal_ideal A ≠ ⊥,
    { exact discrete_valuation_ring.not_a_field A },
    obtain ⟨a, ha⟩ := submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr hA),
    rw submodule.ne_bot_iff,
    use (e a),
    split,
    { erw [local_ring.mem_maximal_ideal, map_mem_nonunits_iff (e : A →+* B),
        ← local_ring.mem_maximal_ideal], 
      exact a.2, },
    { rw map_ne_zero_iff _ (e.injective),
      simp only [ne.def, submodule.coe_eq_zero], exact ha },
  end }