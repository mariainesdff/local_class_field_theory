import data.set.lattice

/-!
# Lattice
This file contains a technical lemma concerning intersections of Iio and Ico in linearly order
sets
-/

lemma set_inter_Iio {α β: Type*} [linear_order β] {X : β → set α} {D N : β} (hND : N ≤ D) :
  (⋂ d ∈ (set.Iio D), X d) = (⋂ d ∈ (set.Iio N), X d) ∩ (⋂ d ∈ (set.Ico N D), X d) :=
begin
  by_cases hND₀ : N = D,
  { haveI : is_empty {d | D ≤ d ∧ d < D},
    { simp only [set.coe_set_of, is_empty_subtype, not_and, not_lt, imp_self, implies_true_iff] },
    have aux : (⋂ (d : β) (x : D ≤ d ∧ d < D), X d) = set.univ,
    { erw set.bInter_eq_Inter {d | D ≤ d ∧ d < D} (λ x _, X x),
      apply set.Inter_of_empty },
    simp only [hND₀, set.mem_Iio, set.mem_Ico, aux, set.inter_univ] },
  { replace hND := lt_of_le_of_ne hND hND₀,
    rw [← set.Inter_inter_distrib, ← max_eq_right (le_refl D), ← set.Iio_union_Ioo
      (min_lt_of_left_lt hND), max_eq_right (le_refl D)],
    congr' with d,
    simp only [set.mem_union, set.mem_Iio, set.mem_Ico, set.mem_Ioo, set.mem_Inter,
      set.mem_inter_iff, and_imp],
    refine ⟨λ h, ⟨λ H, h $ or.inl $ H.trans hND, λ H h_ND, h $ or.inl h_ND⟩,
      λ h H, _⟩,
    rcases H with Ha | Hb,
    by_cases H_Nd : d < N,
    exacts [h.1 H_Nd, h.2 (le_of_not_lt H_Nd) Ha, h.2 (le_of_lt Hb.1) Hb.2] },
end