/-
Copyright (c) 2023 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import discrete_valuation_ring.extensions
import number_theory.ramification_inertia
import ring_theory.dedekind_domain.integral_closure

open local_ring valuation ideal --local_ring
open_locale discrete_valuation classical


/-
TODO:
1. Rename prime/prime'
2. turn hv implicit?
3. Add final results by María Inés
-/
noncomputable theory

universes u w

namespace discrete_valuation

variables (K : Type u) [field K] (hv : valued K ℤₘ₀) (L : Type w) [field L] [algebra K L] 

local notation `K₀` := hv.v.valuation_subring

include hv

/- As an alternative, we could define it as the ideal generated by the coercion of
a generator of `local_ring.maximal_ideal K₀`. -/
-- noncomputable!
@[reducible]
def extended_max_ideal : ideal (integral_closure K₀ L) :=
(map (algebra_map K₀ (integral_closure K₀ L)) (local_ring.maximal_ideal K₀))
/- span {algebra_map K₀ (integral_closure K₀ L)
  (submodule.is_principal.generator (local_ring.maximal_ideal K₀))} -/

variables [is_discrete hv.v] [complete_space K] [finite_dimensional K L]


instance : discrete_valuation_ring (integral_closure K₀ L) := infer_instance
instance : local_ring (integral_closure K₀ L) := infer_instance

lemma extended_max_ideal_ne_zero : 
  extended_max_ideal K hv L ≠ 0 :=
begin
  obtain ⟨π, hπ⟩:= discrete_valuation.exists_uniformizer hv.v, 
  rw [extended_max_ideal, ideal.map, ne.def, zero_eq_bot, span_eq_bot],
  simp only [set.mem_image, set_like.mem_coe, mem_maximal_ideal, mem_nonunits_iff, 
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, not_forall, exists_prop],
  use [π, uniformizer_not_is_unit hv.v hπ],
  rw [map_eq_zero_iff _, ← subring.coe_eq_zero_iff],
  exact (uniformizer_ne_zero hv.v hπ),
  { exact no_zero_smul_divisors.algebra_map_injective _ _,}
end


lemma extended_max_ideal_not_is_unit : ¬ is_unit (extended_max_ideal K hv L) :=
begin
  have h₁ : algebra.is_integral K₀ (integral_closure K₀ L) := 
    le_integral_closure_iff_is_integral.mp (le_refl _),
  have h₂ : ring_hom.ker (algebra_map K₀ (integral_closure K₀ L)) ≤
    local_ring.maximal_ideal K₀,
  { apply local_ring.le_maximal_ideal,
    apply ring_hom.ker_ne_top },
  obtain ⟨Q, hQ_max, hQ⟩ := exists_ideal_over_maximal_of_is_integral h₁
     (local_ring.maximal_ideal K₀) h₂,
  rw [extended_max_ideal, ← hQ, is_unit_iff],
  apply ne_top_of_le_ne_top hQ_max.ne_top,
  apply map_comap_le,
end


instance [is_separable K L] : 
  is_noetherian K₀ (integral_closure K₀ L) :=
by exact is_integral_closure.is_noetherian K₀ K L (integral_closure K₀ L)

lemma ramification_idx_maximal_ne_zero : ne_zero (ramification_idx
  (algebra_map K₀ (integral_closure K₀ L))
  (local_ring.maximal_ideal K₀)
  (local_ring.maximal_ideal (integral_closure K₀ L))) :=
begin
  apply ne_zero.mk,
  apply is_dedekind_domain.ramification_idx_ne_zero (extended_max_ideal_ne_zero K hv L),
  { apply_instance },
  { apply local_ring.le_maximal_ideal,
    intro h,
    rw ← is_unit_iff at h,
    exact extended_max_ideal_not_is_unit K hv L h },
end


lemma ramification_idx_extended_ne_zero : ne_zero
  (ramification_idx
     (algebra_map K₀ (integral_closure K₀ L))
     (local_ring.maximal_ideal K₀) (extended_max_ideal K hv L)) :=
begin
  apply ne_zero.mk,
  have := (((discrete_valuation_ring.tfae (integral_closure K₀ L) _).out 0 6).mp _),
  specialize this (extended_max_ideal K hv L) (extended_max_ideal_ne_zero K hv L),
  apply ramification_idx_ne_zero nat.one_ne_zero,
  { rw [pow_one, extended_max_ideal],
    simp only [le_refl],},
  { rw [← extended_max_ideal, one_add_one_eq_two, not_le],
    apply pow_lt_self,
    apply extended_max_ideal_ne_zero,
    { intro h,
      rw ← is_unit_iff at h,
      exact extended_max_ideal_not_is_unit K hv L h },
    simp only [le_refl] },
  { apply discrete_valuation_ring.not_is_field },
  apply_instance,
end

-- lemma ramification_idx_ne_zero' : ramification_idx
--   (algebra_map K₀ (integral_closure K₀ L))
--   (local_ring.maximal_ideal K₀) (extended_max_ideal K hv L) ≠ 0 :=
-- begin
--   sorry,
--   -- apply is_dedekind_domain.ramification_idx_ne_zero (extended_max_ideal_ne_zero K hv L),
--   -- { apply_instance },
--   -- { apply local_ring.le_maximal_ideal,
--   --   intro h,
--   --   rw ← is_unit_iff at h,
--   --   exact extended_max_ideal_not_is_unit K hv L h },
-- end

noncomputable!
definition algebra_residue_fields : algebra (residue_field K₀)
  (residue_field (integral_closure K₀ L)) := 
begin
  apply quotient.algebra_quotient_of_ramification_idx_ne_zero 
    (algebra_map K₀ (integral_closure K₀ L)) (local_ring.maximal_ideal K₀) _,
  exact ramification_idx_maximal_ne_zero K hv L,
end

-- set_option profiler true

lemma extended_eq_pow_ramification_index : (extended_max_ideal K hv L) 
    = local_ring.maximal_ideal (integral_closure K₀ L) ^
      (ramification_idx (algebra_map K₀ (integral_closure K₀ L)) 
                              (local_ring.maximal_ideal K₀) 
                              (local_ring.maximal_ideal (integral_closure K₀ L))
      ) :=
begin
  have := (((discrete_valuation_ring.tfae (integral_closure K₀ L) _).out 0 6).mp _),
    -- (extended_max_ideal K hv L) (extended_max_ideal_ne_zero K hv L),
  obtain ⟨n, hn⟩ := this (extended_max_ideal K hv L) (extended_max_ideal_ne_zero K hv L),
  rw [hn],
  { congr,
    rw ramification_idx_spec,
    { apply le_of_eq hn },
    { rw [not_le, ← extended_max_ideal, hn],
      apply pow_succ_lt_pow,
      apply discrete_valuation_ring.not_a_field }},
  { apply discrete_valuation_ring.not_is_field },
  { apply_instance },
end

-- lemma extended_eq_pow_ramification_index' : ideal.map (algebra_map K₀ (integral_closure K₀ L))
--       (local_ring.maximal_ideal K₀) = local_ring.maximal_ideal (integral_closure K₀ L) ^
--       (ramification_idx (algebra_map K₀ (integral_closure K₀ L)) 
--                               (local_ring.maximal_ideal K₀) 
--                               (local_ring.maximal_ideal (integral_closure K₀ L))
--       ) :=
-- begin
--   have := (((discrete_valuation_ring.tfae (integral_closure K₀ L) _).out 0 6).mp _),
--   obtain ⟨n, hn⟩ := this (extended_max_ideal K hv L) (extended_max_ideal_ne_zero K hv L),
--   rw [← extended_max_ideal, hn],
--   { congr,
--     rw ramification_idx_spec,
--     { rw [← extended_max_ideal],
--       apply le_of_eq hn },
--     { rw [not_le, ← extended_max_ideal, hn],
--       apply pow_succ_lt_pow,
--       apply discrete_valuation_ring.not_a_field }},
--   { apply discrete_valuation_ring.not_is_field },
--   { apply_instance, },
-- end

-- lemma minchia : @submodule.quotient_rel (integral_closure K₀ L) (integral_closure K₀ L) _ _ _
--   (extended_max_ideal K hv L) = @submodule.quotient_rel (integral_closure K₀ L)
--   (integral_closure K₀ L) _ _ _
--   (local_ring.maximal_ideal (integral_closure K₀ L) ^
--       (ramification_idx (algebra_map K₀ (integral_closure K₀ L)) 
--                               (local_ring.maximal_ideal K₀) 
--                               (local_ring.maximal_ideal (integral_closure K₀ L))
--       )) :=
-- begin
--   rw extended_max_ideal,
--   rw extended_eq_pow_ramification_index',
-- end

@[reducible]
def algebra_mod_power_e : algebra (residue_field K₀)
    ((integral_closure K₀ L) ⧸ (local_ring.maximal_ideal (integral_closure K₀ L) ^ 
    (ramification_idx (algebra_map K₀ (integral_closure K₀ L)) 
                              (local_ring.maximal_ideal K₀) 
                              (local_ring.maximal_ideal (integral_closure K₀ L))
    ))) :=
begin
  apply ideal.quotient.algebra_quotient_of_ramification_idx_ne_zero 
    (algebra_map K₀ (integral_closure K₀ L)) _ _,
  -- have := ramification_idx_extended_ne_zero K hv L,
  rw ← extended_eq_pow_ramification_index,
  apply ramification_idx_extended_ne_zero,
  -- { rw pow_one,
  --   simp only [le_refl] },
  -- { rw [not_le, one_add_one_eq_two, ← extended_eq_pow_ramification_index],
  --   apply pow_lt_self,
  --   { apply extended_max_ideal_ne_zero },
  --   { rw [ne.def,← is_unit_iff],
  --     apply extended_max_ideal_not_is_unit, },
  --   { simp only [le_refl]}},
  -- { exact nat.one_ne_zero },
end


@[reducible]
def algebra_mod_extended : algebra (residue_field K₀)
  ((integral_closure K₀ L) ⧸ (extended_max_ideal K hv L)) :=
begin
  rw [extended_eq_pow_ramification_index],
  exact (algebra_mod_power_e K hv L),
end

local attribute [instance] algebra_mod_power_e algebra_mod_extended

lemma algebra_map_comp_extended : (algebra_map (residue_field K₀)
    ((integral_closure K₀ L) ⧸ (local_ring.maximal_ideal (integral_closure K₀ L) ^ 
    (ramification_idx (algebra_map K₀ (integral_closure K₀ L)) 
                              (local_ring.maximal_ideal K₀) 
                              (local_ring.maximal_ideal (integral_closure K₀ L)))))
  ) ∘ (ideal.quotient.mk (local_ring.maximal_ideal K₀)) =
  ideal.quotient.mk ((local_ring.maximal_ideal (integral_closure K₀ L) ^ 
    (ramification_idx (algebra_map K₀ (integral_closure K₀ L)) 
                              (local_ring.maximal_ideal K₀) 
                              (local_ring.maximal_ideal (integral_closure K₀ L)))))
  ∘ (algebra_map K₀ (integral_closure K₀ L)) :=
begin
  refl,
end

lemma algebra_map_comp_power_e : (algebra_map (residue_field K₀)
    ((integral_closure K₀ L) ⧸ (extended_max_ideal K hv L))
      ) ∘ (ideal.quotient.mk (local_ring.maximal_ideal K₀)) =
  ideal.quotient.mk (extended_max_ideal K hv L) ∘ (algebra_map K₀ (integral_closure K₀ L)) :=
begin
  convert (algebra_map_comp_extended K hv L),
  any_goals {rw extended_eq_pow_ramification_index},
  { simp only [algebra_mod_extended],
    simp only [eq_mpr_eq_cast, ← cast_cast, cast_heq], },
end

lemma algebra_map_comp_power_e_apply (a : K₀) : (algebra_map (residue_field K₀)
    ((integral_closure K₀ L) ⧸ (extended_max_ideal K hv L))
      ) (ideal.quotient.mk (local_ring.maximal_ideal K₀) a) =
  ideal.quotient.mk (extended_max_ideal K hv L) (algebra_map K₀ (integral_closure K₀ L) a) :=
begin
  have : ((algebra_map (residue_field K₀)
    ((integral_closure K₀ L) ⧸ (extended_max_ideal K hv L))
      ) ∘ (ideal.quotient.mk (local_ring.maximal_ideal K₀))) a =
  (ideal.quotient.mk (extended_max_ideal K hv L) ∘ (algebra_map K₀ (integral_closure K₀ L))) a,
  rwa algebra_map_comp_power_e,
end

-- lemma primo''_apply (a : (residue_field K₀)) : (algebra_map (residue_field K₀)
--     ((integral_closure K₀ L) ⧸ (extended_max_ideal K hv L))
--       ) a =
--   ideal.quotient.mk (extended_max_ideal K hv L) (algebra_map (residue_field K₀)
--     (residue_field (integral_closure K₀ L)) a) :=
-- begin
--   have : ((algebra_map (residue_field K₀)
--     ((integral_closure K₀ L) ⧸ (extended_max_ideal K hv L))
--       ) ∘ (ideal.quotient.mk (local_ring.maximal_ideal K₀))) a =
--   (ideal.quotient.mk (extended_max_ideal K hv L) ∘ (algebra_map K₀ (integral_closure K₀ L))) a,
--   rw primo',
--   exact this,
-- end

noncomputable!
definition scalar_tower_extended : is_scalar_tower K₀ (residue_field K₀)
  ((integral_closure K₀ L) ⧸ (extended_max_ideal K hv L)) :=
begin
  refine is_scalar_tower.of_algebra_map_eq (λ a, _),
  have algebra_map_comp : algebra_map K₀ ((integral_closure K₀ L) ⧸ (extended_max_ideal K hv L)) a =
    (ideal.quotient.mk (extended_max_ideal K hv L) ∘ (algebra_map K₀ (integral_closure K₀ L))) a,
  { refl },
  have algebra_map_eq_quot_mk : algebra_map K₀ (residue_field K₀) a =
    (ideal.quotient.mk (local_ring.maximal_ideal K₀)) a,
  { refl },
  rw [algebra_map_comp, ← algebra_map_comp_power_e, algebra_map_eq_quot_mk],
end

definition scalar_tower_power_e : is_scalar_tower K₀ (residue_field K₀)
  ((integral_closure K₀ L) ⧸ (local_ring.maximal_ideal (integral_closure K₀ L) ^ 
    (ramification_idx (algebra_map K₀ (integral_closure K₀ L)) 
                              (local_ring.maximal_ideal K₀) 
                              (local_ring.maximal_ideal (integral_closure K₀ L))
    ))) :=
begin
  refine is_scalar_tower.of_algebra_map_eq (λ a, _),
  have algebra_map_comp : algebra_map K₀ ((integral_closure K₀ L) ⧸
    (local_ring.maximal_ideal (integral_closure K₀ L) ^ 
    (ramification_idx (algebra_map K₀ (integral_closure K₀ L)) 
                              (local_ring.maximal_ideal K₀) 
                              (local_ring.maximal_ideal (integral_closure K₀ L))))) a =
    (ideal.quotient.mk ((local_ring.maximal_ideal (integral_closure K₀ L) ^ 
    (ramification_idx (algebra_map K₀ (integral_closure K₀ L)) 
                              (local_ring.maximal_ideal K₀) 
                              (local_ring.maximal_ideal (integral_closure K₀ L))
    ))) ∘ (algebra_map K₀ (integral_closure K₀ L))) a,
  { refl },
  have algebra_map_eq_quot_mk : algebra_map K₀ (residue_field K₀) a =
    (ideal.quotient.mk (local_ring.maximal_ideal K₀)) a,
  refl,
  rw [algebra_map_comp, ← algebra_map_comp_extended, algebra_map_eq_quot_mk],
end

-- noncomputable!
-- def quotient_alg_equiv : ((integral_closure K₀ L) ⧸ (extended_max_ideal K hv L))
--   ≃ₗ[residue_field K₀]
--   ((integral_closure K₀ L) ⧸ (local_ring.maximal_ideal (integral_closure K₀ L) ^ 
--     (ramification_idx (algebra_map K₀ (integral_closure K₀ L)) 
--                               (local_ring.maximal_ideal K₀) 
--                               (local_ring.maximal_ideal (integral_closure K₀ L))))) :=
-- begin
--   -- letI := scalar_tower_extended K hv L,
--   -- letI := scalar_tower_power K hv L,--needed? if not, remove declaration above

--   -- let f :=  ideal.quotient_equiv_alg_of_eq K₀ (extended_eq_pow_ramification_index K hv L),
--   -- let φ := f.to_linear_equiv,--forse usare submodule.quot_equiv_of_eq
--   let ϕ := submodule.quot_equiv_of_eq _ _ (extended_eq_pow_ramification_index K hv L),
--   let ψ :
--   ((integral_closure K₀ L) ⧸ (extended_max_ideal K hv L))
--   →ₗ[residue_field K₀]
--   ((integral_closure K₀ L) ⧸ (local_ring.maximal_ideal (integral_closure K₀ L) ^ 
--     (ramification_idx (algebra_map K₀ (integral_closure K₀ L)) 
--                               (local_ring.maximal_ideal K₀) 
--                               (local_ring.maximal_ideal (integral_closure K₀ L))))),
--   use ϕ,
--   sorry,
--   { rintros ⟨a⟩ v,
    

--   },

-- end

-- #exit

--   let g :
--   ((integral_closure K₀ L) ⧸ (extended_max_ideal K hv L))
--   →ₐ[residue_field K₀]
--   ((integral_closure K₀ L) ⧸ (local_ring.maximal_ideal (integral_closure K₀ L) ^ 
--     (ramification_idx (algebra_map K₀ (integral_closure K₀ L)) 
--                               (local_ring.maximal_ideal K₀) 
--                               (local_ring.maximal_ideal (integral_closure K₀ L))))),
--   use λ x, f x,
--   simp only [_root_.map_one],
--   sorry,
--   sorry,
--   sorry,
--   -- any_goals {simp},
--   { intro a,
--     -- squeeze_simp,
    
--     --rintro ⟨a⟩,
--     -- rw primo'_apply K hv L a,

--   },
--   -- use f.1,  
--   -- let := @alg_equiv.of_bijective (residue_field K₀) _ _ _ _ _ (algebra_mod_extended K hv L)
--   --   (algebra_mod_power_e K hv L),
  


--   -- let f := ideal.quotient_equiv_alg_of_eq (extended_eq_pow_ramification_index K hv L),
--   -- let f := ideal.quot_equiv_of_eq (extended_eq_pow_ramification_index K hv L),
--   -- -- let g := f.to_semilinear_equiv,
--   -- fconstructor,
--   -- use f.1,
--   -- use f.map_add,
--   -- { rintros a ⟨v⟩,
--   --   squeeze_simp,
--   --   rw submodule.quotient.mk'_eq_mk,
--   --   rw ← ideal.quotient.mk_eq_mk,
--   --   simp only [ring_equiv.to_fun_eq_coe, ring_hom.id_apply],
--   --   have := ideal.quot_equiv_of_eq_mk (extended_eq_pow_ramification_index K hv L) v,
--   --   -- have hfg : f v = g v := rfl,
--   --   -- rw hfg,
--   --   -- rw ← g.map_smulₛₗ,
--   --   -- haveI := ring_hom_inv_pair.of_ring_equiv f,
--   --   -- -- haveI := ring_hom_inv_pair.symm (↑f : R →+* S) (f.symm : S →+* R),
--   --   -- rw hfg,
    

--   -- },
--   -- use f.inv_fun,
--   -- use f.left_inv,
--   -- use f.right_inv,
-- end

noncomputable!
def quotient_linear_iso : ((integral_closure K₀ L) ⧸ (extended_max_ideal K hv L)) ≃ₗ[residue_field K₀]
  ((integral_closure K₀ L) ⧸ (local_ring.maximal_ideal (integral_closure K₀ L) ^ 
    (ramification_idx (algebra_map K₀ (integral_closure K₀ L)) 
                              (local_ring.maximal_ideal K₀) 
                              (local_ring.maximal_ideal (integral_closure K₀ L))
    ))) :=
begin
  -- letI st_ext := scalar_tower_extended K hv L,
  let f := (submodule.quot_equiv_of_eq _ _
    (extended_eq_pow_ramification_index K hv L)).restrict_scalars K₀,
  let g :
  ((integral_closure K₀ L) ⧸ (extended_max_ideal K hv L))
  →ₗ[residue_field K₀]
  ((integral_closure K₀ L) ⧸ (local_ring.maximal_ideal (integral_closure K₀ L) ^ 
    (ramification_idx (algebra_map K₀ (integral_closure K₀ L)) 
                              (local_ring.maximal_ideal K₀) 
                              (local_ring.maximal_ideal (integral_closure K₀ L))))),
  use λ x, f x,
  { apply f.map_add },
  { rintros ⟨a⟩ v,
    simp only [submodule.quotient.quot_mk_eq_mk, quotient.mk_eq_mk, embedding_like.apply_eq_iff_eq],
    have algebra_map_eq_quot_mk : algebra_map K₀ (residue_field K₀) a = (ideal.quotient.mk
      (local_ring.maximal_ideal K₀)) a,
    { refl },
    let scalar_tower_v := (scalar_tower_extended K hv L).1 a 1 v,
    let scalar_tower_fv := (scalar_tower_power_e K hv L).1 a 1 (f v),
    rw [← algebra.algebra_map_eq_smul_one a, one_smul, algebra_map_eq_quot_mk] at 
      scalar_tower_v scalar_tower_fv,
    -- rw one_smul at scalar_tower_v,
    -- rw algebra_map_eq_quot_mk at scalar_tower_v,
    rw scalar_tower_v,
    rw ring_hom.id_apply,
    
    -- rw [← algebra.algebra_map_eq_smul_one a] at scalar_tower_fv,
    -- rw one_smul at scalar_tower_fv,
    -- rw algebra_map_eq_quot_mk at scalar_tower_fv,
    rw scalar_tower_fv,
    apply f.map_smul  },
  have h : function.bijective g,
  apply g.bijective,
  use linear_equiv.of_bijective g h,
end

local attribute [instance] algebra_residue_fields

lemma finite_dimensional_pow [is_separable K L] :  finite_dimensional (residue_field K₀)
    ((map
            (ideal.quotient.mk
               (local_ring.maximal_ideal (integral_closure K₀ L) ^
                  ramification_idx
                    (algebra_map K₀
                       (integral_closure K₀ L))
                    (local_ring.maximal_ideal K₀)
                    (local_ring.maximal_ideal (integral_closure K₀ L))))
            (local_ring.maximal_ideal (integral_closure K₀ L) ^ 0)) ⧸
       linear_map.range
         (pow_quot_succ_inclusion
            (algebra_map K₀ (integral_closure K₀ L))
            (local_ring.maximal_ideal K₀)
            (local_ring.maximal_ideal (integral_closure K₀ L))
            0)) :=
begin
  have aux : finite_dimensional.finrank (K₀ ⧸ local_ring.maximal_ideal K₀)
    ((integral_closure K₀ L) ⧸ (extended_max_ideal K hv L)) = finite_dimensional.finrank K L,
  { apply @finrank_quotient_map K₀ _ (integral_closure K₀ L) _ (local_ring.maximal_ideal K₀)
    _ K _ _ _ L _ _ (integral_closure.is_fraction_ring_of_finite_extension K L)
    _ _ _ _ _ _ _ _ _ _ },
  haveI : finite_dimensional (residue_field K₀)
    ((integral_closure K₀ L) ⧸ (extended_max_ideal K hv L)),
  { suffices : 0 < finite_dimensional.finrank K L,
    { apply finite_dimensional.finite_dimensional_of_finrank,
      convert this using 1,
      convert aux,
      dsimp only [extended_max_ideal],--needed?
      apply algebra.algebra_ext,
      rintro ⟨a⟩,
      simp only [submodule.quotient.quot_mk_eq_mk, quotient.mk_eq_mk,
        algebra_map_comp_power_e_apply K hv L a, ← quotient.algebra_map_quotient_map_quotient],
      refl },
    { rw finite_dimensional.finrank_pos_iff_exists_ne_zero,
      use 1,
      apply one_ne_zero } },
  replace aux : finite_dimensional (residue_field K₀)
              (map (ideal.quotient.mk
                      ((local_ring.maximal_ideal (integral_closure K₀ L)) ^
                      (ramification_idx
                      (algebra_map K₀ (integral_closure K₀ L))
                      (local_ring.maximal_ideal K₀)
                      (local_ring.maximal_ideal (integral_closure K₀ L))
                      ))
                    )
              ((local_ring.maximal_ideal (integral_closure K₀ L)) ^ 0)),
    { rw [pow_zero, one_eq_top, ideal.map_top],
      haveI := (quotient_linear_iso K hv L).finite_dimensional,
      apply (@submodule.top_equiv (residue_field K₀) 
        ((integral_closure K₀ L) ⧸ (local_ring.maximal_ideal (integral_closure K₀ L) ^ 
        (ramification_idx (algebra_map K₀ (integral_closure K₀ L)) 
                              (local_ring.maximal_ideal K₀) 
                              (local_ring.maximal_ideal (integral_closure K₀ L))
        ))) _ _ _).symm.finite_dimensional },
    dsimp only [residue_field],--needed?
    apply @finite_dimensional.finite_dimensional_quotient (residue_field K₀) _ _ _ _ aux,
end

/-The lemma `finrank_quotient_map` has an implicit variable `S` that should probably be made
explicit
-/
noncomputable!
lemma finite_dimensional_residue_field_of_integral_closure [is_separable K L] : 
  finite_dimensional (residue_field K₀) (residue_field (integral_closure K₀ L)) :=
begin
  let alg := (algebra_residue_fields K hv L),
  dsimp only [residue_field] at alg,
  letI := alg,
  haveI := ramification_idx_maximal_ne_zero K hv L,
  have zero_lt : 0 < (ramification_idx (algebra_map K₀ (integral_closure K₀ L)) 
                              (local_ring.maximal_ideal K₀) 
                              (local_ring.maximal_ideal (integral_closure K₀ L))), 
  { apply nat.pos_of_ne_zero,
    exact (ramification_idx_maximal_ne_zero K hv L).1 },
  let surj := quotient_range_pow_quot_succ_inclusion_equiv (algebra_map K₀
    (integral_closure K₀ L)) (local_ring.maximal_ideal K₀)
    (local_ring.maximal_ideal (integral_closure K₀ L)) (discrete_valuation_ring.not_a_field _)
      zero_lt,
  refine @linear_equiv.finite_dimensional (residue_field K₀) _ _ _ _
    (residue_field (integral_closure K₀ L)) _ _ surj (finite_dimensional_pow K hv L),
end


end discrete_valuation