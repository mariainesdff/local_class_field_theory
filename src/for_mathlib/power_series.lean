import field_theory.finite.galois_field
import ring_theory.dedekind_domain.adic_valuation
import ring_theory.dedekind_domain.integral_closure

import ring_theory.valuation.tfae

noncomputable theory

lemma power_series.coeff_zero_eq_eval {K : Type*} [semiring K] (f : power_series K) :
  (power_series.coeff K 0) f = f 0 :=
by simp only [power_series.coeff, mv_power_series.coeff, linear_map.coe_proj,
  function.eval_apply, finsupp.single_zero]

instance power_series.is_principal_ideal_ring (K : Type*) [field K] : 
  is_principal_ideal_ring (power_series K) := 
begin
  rw is_principal_ideal_ring_iff,
  intros I,
  by_cases hI : I = ⊥,
  { rw hI,
    exact bot_is_principal, },
  { have hI': ∃ n : ℕ, I = ideal.span{power_series.X^n},
    { -- n is the minimum order of the elements in I (TODO: finish proof)
      sorry },
    obtain ⟨n, hn⟩ := hI',
    rw hn,
    use [power_series.X^n, rfl] } 
end

instance power_series.is_noetherian_ring (K : Type*) [field K]: 
  is_noetherian_ring (power_series K) :=
principal_ideal_ring.is_noetherian_ring


lemma power_series.maximal_ideal_eq_span_X {K : Type*} [field K] :
  local_ring.maximal_ideal (power_series K) = ideal.span {power_series.X} :=
begin
  have hX : (ideal.span {(power_series.X : power_series K)}).is_maximal,
  { rw ideal.is_maximal_iff,
    split,
    { rw ideal.mem_span_singleton,
      exact prime.not_dvd_one power_series.X_prime, },
    intros I f hI hfX hfI,
    rw [ideal.mem_span_singleton, power_series.X_dvd_iff] at hfX,
    have hfI0 : power_series.C K (f 0) ∈ I,
    { have : power_series.C K (f 0) = f - (f - power_series.C K (f 0)),
      { rw sub_sub_cancel, },
      rw this,
      apply ideal.sub_mem I hfI,
      apply hI,
      rw [ideal.mem_span_singleton, power_series.X_dvd_iff, map_sub, power_series.constant_coeff_C,
        ← power_series.coeff_zero_eq_constant_coeff_apply, power_series.coeff_zero_eq_eval, 
        sub_eq_zero] },
    rw ← ideal.eq_top_iff_one,
    apply ideal.eq_top_of_is_unit_mem I hfI0 (is_unit.map (power_series.C K) (ne.is_unit hfX)) },
  rw local_ring.eq_maximal_ideal hX,
end

lemma power_series.maximal_ideal_is_principal (K : Type*) [field K] :
  submodule.is_principal (local_ring.maximal_ideal (power_series K)) :=
begin
  rw [power_series.maximal_ideal_eq_span_X, submodule.is_principal_iff],
  exact ⟨power_series.X, rfl⟩,
end

lemma power_series.not_is_field (R : Type*) [comm_ring R] [nontrivial R] :
  ¬ is_field (power_series R) :=
begin
  nontriviality R,
  rw ring.not_is_field_iff_exists_ideal_bot_lt_and_lt_top,
  use ideal.span {power_series.X},
  split,
  { rw [bot_lt_iff_ne_bot, ne.def, ideal.span_singleton_eq_bot],
    exact power_series.X_ne_zero, },
  { rw [lt_top_iff_ne_top, ne.def, ideal.eq_top_iff_one, ideal.mem_span_singleton,
      power_series.X_dvd_iff, power_series.constant_coeff_one],
    exact one_ne_zero },
end


-- really slow (tfae?)
noncomputable! instance power_series.discrete_valuation_ring (K : Type*) [field K] : 
  discrete_valuation_ring (power_series K) := 
begin
  rw list.tfae.out (discrete_valuation_ring.tfae (power_series K) 
    (power_series.not_is_field K)) 0 4,
  exact power_series.maximal_ideal_is_principal K,
end

noncomputable! instance power_series.is_dedekind_domain (K : Type*) [field K] : 
  is_dedekind_domain (power_series K) := infer_instance
