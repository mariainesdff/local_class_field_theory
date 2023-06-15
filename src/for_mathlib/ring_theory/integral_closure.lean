import ring_theory.integral_closure

open ring_hom

theorem mem_integral_closure_iff (R A : Type*) [comm_ring R] [comm_ring A] [algebra R A] {a : A} :
  a ∈ integral_closure R A ↔ is_integral R a :=
iff.rfl

theorem is_integral_iff_of_equiv {R S T : Type*} [comm_ring R] [comm_ring S] [comm_ring T] 
  [algebra R S] [algebra T S] (φ : R ≃+* T)
  (h : (algebra_map T S).comp φ.to_ring_hom = (algebra_map R S)) (a : S) :
  is_integral R a ↔ is_integral T a :=
begin
  split; intro ha,
  { rw ← id_apply a, 
    refine is_integral_map_of_comp_eq_of_is_integral φ.to_ring_hom (ring_hom.id S) _ ha,
    rw [id_comp, h] },
  { rw ← id_apply a, 
    refine is_integral_map_of_comp_eq_of_is_integral φ.symm.to_ring_hom (ring_hom.id S) _ ha,
    rw [id_comp, ← h, comp_assoc, ring_equiv.to_ring_hom_comp_symm_to_ring_hom, comp_id] }
end
