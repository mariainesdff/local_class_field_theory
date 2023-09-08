import order.filter.basic
import topology.uniform_space.cauchy

/-
# Main Results

This file contains generalities about Cauchy filters (and convergence theoref) in spaces endowed
with the discrete uniformity. The main results are
* `cauchy_discrete_is_constant` stating that a Cauchy filter in a discrete space is actually a
principal filter
* `ne_bot_unique_principal` saying that in a non-empty discrete space, two principal filters that
contain a non-trivial filter coincide
-/


namespace set

lemma prod_subset_diag_singleton_left {X : Type*} {S T : set X} (hS : S.nonempty)
  (hT : T.nonempty) (h_diag : S ×ˢ T ⊆ id_rel) : ∃ x, S = {x} :=
begin
  rcases ⟨hS, hT⟩ with ⟨⟨s, hs⟩, ⟨t, ht⟩⟩,
  refine ⟨s, (eq_singleton_iff_nonempty_unique_mem.mpr ⟨⟨s, hs⟩, _⟩)⟩,
  intros x hx,
  rw prod_subset_iff at h_diag,
  replace hs := h_diag s hs t ht, 
  replace hx := h_diag x hx t ht,
  simp only [id_rel, mem_set_of_eq] at hx hs,
  rwa [← hs] at hx,
end

lemma prod_subset_diag_singleton_right {X : Type*} {S T : set X} (hS : S.nonempty) (hT : T.nonempty) 
  (h_diag : S ×ˢ T ⊆ id_rel) : ∃ x, T = {x} :=
begin
  rw set.prod_subset_iff at h_diag,
  replace h_diag := λ x hx y hy, (h_diag y hy x hx).symm,
  exact prod_subset_diag_singleton_left hT hS ((prod_subset_iff).mpr h_diag),
end


lemma prod_subset_diag_singleton_eq {X : Type*} {S T : set X} (hS : S.nonempty) (hT : T.nonempty) 
  (h_diag : S ×ˢ T ⊆ id_rel) : ∃ x, S = {x} ∧ T = {x} :=
begin
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := ⟨prod_subset_diag_singleton_left hS hT h_diag,
    prod_subset_diag_singleton_right hS hT h_diag⟩,
  refine ⟨x, ⟨hx, _⟩⟩,
  rw [hy, set.singleton_eq_singleton_iff],
  exact (set.prod_subset_iff.mp h_diag x (by simp only [hx, set.mem_singleton]) y 
    (by simp only [hy, set.mem_singleton])).symm,
end

end set

section cauchy_discrete

open filter set
open_locale filter topology

lemma cauchy_discrete_le_principal {X : Type*} {uX : uniform_space X}
(hX : uniformity X = 𝓟 id_rel) {α : filter X} (hα : cauchy α) : ∃ x : X, α ≤ 𝓟 {x} :=
begin
  rcases hα with ⟨α_ne_bot, α_le⟩,
  rw [filter.le_def] at α_le,
  specialize α_le id_rel,
  simp only [filter.le_def, hX, mem_principal, id_rel_subset, mem_id_rel, eq_self_iff_true,
    implies_true_iff, forall_true_left, filter.mem_prod_iff] at α_le,
  obtain ⟨_, ⟨hS, ⟨_, ⟨hT, H⟩⟩⟩⟩ := α_le,
  obtain ⟨x, hx⟩ := prod_subset_diag_singleton_left (@filter.nonempty_of_mem X α α_ne_bot _ hS)
    (@filter.nonempty_of_mem _ _ α_ne_bot _ hT) H,
  use x,
  rwa [filter.le_principal_iff, ← hx],
end

/-- The constant to which a Cauchy filter in a discrete space converges.
-/
noncomputable
definition cauchy_discrete_is_constant {X : Type*} {uX : uniform_space X}
  (hX : uniformity X = 𝓟 id_rel) {α : filter X} (hα : cauchy α) : X :=
(cauchy_discrete_le_principal hX hα).some

lemma cauchy_discrete_le  {X : Type*} {uX : uniform_space X} 
  (hX : uniformity X = 𝓟 id_rel) {α : filter X} (hα : cauchy α) : 
  α ≤ 𝓟 {cauchy_discrete_is_constant hX hα} := Exists.some_spec (cauchy_discrete_le_principal hX hα)

lemma ne_bot_unique_principal {X : Type*} [uniform_space X] (hX : uniformity X = 𝓟 id_rel)
  {α : filter X} (hα : α.ne_bot) {x y : X} (hx : α ≤ 𝓟 {x}) (hy : α ≤ 𝓟 {y}) : x = y :=
begin
  have h_disc : discrete_topology X,
  apply discrete_topology_of_discrete_uniformity hX,
  have t2X := @discrete_topology.to_t2_space X _ h_disc,
  apply @eq_of_nhds_ne_bot X _ t2X x y,
  simp only [discrete_topology_iff_nhds.mp h_disc],
  apply @ne_bot_of_le _ _ _ hα,
  simp only [le_inf_iff, le_pure_iff],
  exact ⟨le_principal_iff.mp hx, le_principal_iff.mp hy⟩,
end

end cauchy_discrete