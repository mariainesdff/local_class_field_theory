import discrete_valuation_ring.extensions
import number_theory.ramification_inertia
import ring_theory.dedekind_domain.integral_closure

/-! # The residue field of a DVR
In this file we consider a finite extension `L/K` of a discretely valued field `K`. By the results
in `discrete_valuation_ring.basic`, the unit ball `K₀` is a DVR and the main result we prove is that
(under the assumption that `L/K` is separable, currently needed to ensure that the integral closure
of `K₀` in `L` is finite over `K₀`, but that should potentially be removed), the residue field of
the integral closure of `K₀` in `L` is finite dimensional over the residue field of `K₀`. As a
consequence, when the residue field of `K₀` is finite, so is the residue field of `L₀`

## Main definitions
* `extended_max_ideal` The ideal in `L` extending the maximal ideal of `K₀.
* `quotient_linear_iso` The equivalence as vector spaces over the residue field of the base of
  * the quotient of the integral closure of `K₀` modulo the extension of the maximal ideal below;
    and
  * the quotient of the integral closure of `K₀` modulo the `e`-th power of the maximal idal above;
  induced by the equality of the two ideals proved in `extended_eq_pow_ramification_index`
* `finite_residue_field_of_integral_closure` and `finite_residue_field_of_unit_ball` are the proofs
  that whenever `L/K` is separable, and the residue field of `K₀` is finite, so is also the residue
  field both of the integral closure of `K₀` in `L` and of the unit ball `L₀`.

## Main results
* `ramification_idx_maximal_ne_zero` The ramification index of the maximal ideal in the integral
  closure of `K₀` in `L` over the maximal ideal of `K₀` is non zero.
* `ramification_idx_extended_ne_zero` The ramification index of the extension of the maximal ideal
  of `K₀` to the ring of integers of `L`, over the maximal ideal of `K₀` is non zero.
* `extended_eq_pow_ramification_index` The equality between the the extension of the maximal ideal
  of `K₀` to the ring of integers of `L` and the `e`-th power of the maximal ideal in this integral
  closure, where `e ≠ 0` is the ramification index.
* `finite_dimensional_residue_field_of_integral_closure` When `L/K` is (finite and) separable, the
  residue field of the integral closure of `K₀` in `L` (or, equivalently, of `L₀` in view of the
  declaration `integral_closure_eq_integer`  proven in `discrete_valuation_ring.extensions`) is
  finite dimensional over the residue field of `K₀`.


## Implementation details
* The file compiles slowly, in particular the declaration `finite_dimensional_pow` seems extremely
  expensive. **FAE: APPROPRIATE?**
* **FAE: something about quotients?**
* `algebra_mod_power_e` is an `instance` while `algebra_mod_extended` is only a `definition`, turned
  into a `local instance`. This is because the type-class inference mechanism seems unable to find
  the second instance automatically even if it is marked as such, so it has sometimes to be called
  explicitely.
* To prove that the residue field of `L₀` is finite (under suitable assumptions) we first prove that
  the residue field of the integral closure of `K₀` in `L` is finite, and then we use
  `integral_closure_eq_integer` proven in `discrete_valuation_ring.extensions` to transfer this
  finiteness to `L₀`.
-/


open local_ring valuation ideal
open_locale discrete_valuation classical

noncomputable theory

universes u w

namespace discrete_valuation

variables (K : Type u) [field K] [hv : valued K ℤₘ₀] (L : Type w) [field L] [algebra K L] 

local notation `K₀` := hv.v.valuation_subring

include hv

/-- The ideal in the ìntegers of `L` obtained by extending the maximal ideal of `K₀`-/
@[reducible]
def extended_max_ideal : ideal (integral_closure K₀ L) :=
(map (algebra_map K₀ (integral_closure K₀ L)) (local_ring.maximal_ideal K₀))

lemma extended_max_ideal_not_is_unit : ¬ is_unit (extended_max_ideal K L) :=
begin
  have h₁ : algebra.is_integral K₀ (integral_closure K₀ L) := 
    le_integral_closure_iff_is_integral.mp (le_refl _),
  have h₂ : ring_hom.ker (algebra_map K₀ (integral_closure K₀ L)) ≤
    local_ring.maximal_ideal K₀,
  { exact local_ring.le_maximal_ideal (ring_hom.ker_ne_top _), },
  obtain ⟨Q, hQ_max, hQ⟩ := exists_ideal_over_maximal_of_is_integral h₁
     (local_ring.maximal_ideal K₀) h₂,
  rw [extended_max_ideal, ← hQ, is_unit_iff],
  exact ne_top_of_le_ne_top hQ_max.ne_top map_comap_le,
end


variables [is_discrete hv.v]

lemma extended_max_ideal_ne_zero : 
  extended_max_ideal K L ≠ 0 :=
begin
  obtain ⟨π, hπ⟩ := discrete_valuation.exists_uniformizer_of_discrete hv.v, 
  rw [extended_max_ideal, ideal.map, ne.def, zero_eq_bot, span_eq_bot],
  simp only [set.mem_image, set_like.mem_coe, mem_maximal_ideal, mem_nonunits_iff, 
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, not_forall, exists_prop],
  use [π, uniformizer_not_is_unit hv.v hπ],
  rw [map_eq_zero_iff _, ← subring.coe_eq_zero_iff],
  exact (uniformizer_ne_zero hv.v hπ),
  { exact no_zero_smul_divisors.algebra_map_injective _ _ }
end


variables [finite_dimensional K L]


instance [is_separable K L] : is_noetherian K₀ (integral_closure K₀ L) :=
is_integral_closure.is_noetherian K₀ K L (integral_closure K₀ L)

variables [complete_space K] 


-- @[priority 10000]
-- lemma dd : is_dedekind_domain (integral_closure K₀ L) :=
-- @is_principal_ideal_ring.is_dedekind_domain _ _ _
--   (@discrete_valuation_ring.to_is_principal_ideal_ring _ _ _
--   (integral_closure.discrete_valuation_ring_of_finite_extension K L))


lemma ramification_idx_maximal_ne_zero : ne_zero (ramification_idx
  (algebra_map K₀ (integral_closure K₀ L)) (local_ring.maximal_ideal K₀)
  (local_ring.maximal_ideal (integral_closure K₀ L))) :=
begin
  apply ne_zero.mk,
  apply is_dedekind_domain.ramification_idx_ne_zero (extended_max_ideal_ne_zero K L),
  { apply is_maximal.is_prime' },
  { apply local_ring.le_maximal_ideal,
    intro h,
    apply extended_max_ideal_not_is_unit K L (is_unit_iff.mpr h) },
end

lemma ramification_idx_extended_ne_zero : 
  ne_zero (ramification_idx (algebra_map K₀ (integral_closure K₀ L))
    (local_ring.maximal_ideal K₀) (extended_max_ideal K L)) :=
begin
  apply ne_zero.mk,
  apply ramification_idx_ne_zero nat.one_ne_zero,
  { rw [pow_one, extended_max_ideal],
    exact le_refl _ },
  { rw [← extended_max_ideal, one_add_one_eq_two, not_le],
    apply pow_lt_self,
    apply extended_max_ideal_ne_zero,
    { intro h,
      rw ← is_unit_iff at h,
      exact extended_max_ideal_not_is_unit K L h },
    exact le_refl _ }
end


/-- The residue field of `L` is an algebra over the residue field of `K`-/
noncomputable!
def algebra_residue_fields : algebra (residue_field K₀)
  (residue_field (integral_closure K₀ L)) := 
begin
  apply quotient.algebra_quotient_of_ramification_idx_ne_zero 
    (algebra_map K₀ (integral_closure K₀ L)) (local_ring.maximal_ideal K₀) _,
  exact ramification_idx_maximal_ne_zero K L,
end


lemma extended_eq_pow_ramification_index : (extended_max_ideal K L) 
    = local_ring.maximal_ideal (integral_closure K₀ L) ^
      (ramification_idx (algebra_map K₀ (integral_closure K₀ L)) 
                              (local_ring.maximal_ideal K₀) 
                              (local_ring.maximal_ideal (integral_closure K₀ L))
      ) :=
begin
  have := (((discrete_valuation_ring.tfae (integral_closure K₀ L) _).out 0 6).mp _),
  obtain ⟨n, hn⟩ := this (extended_max_ideal K L) (extended_max_ideal_ne_zero K L),
  rw [hn],
  { apply congr_arg,
    rw ramification_idx_spec,
    { exact le_of_eq hn },
    { rw [not_le, ← extended_max_ideal, hn],
      apply pow_succ_lt_pow,
      exact discrete_valuation_ring.not_a_field _ }},
  { exact discrete_valuation_ring.not_is_field _ },
  { apply_instance },
end

instance algebra_mod_power_e : algebra (residue_field K₀)
    ((integral_closure K₀ L) ⧸ (local_ring.maximal_ideal (integral_closure K₀ L) ^ 
    (ramification_idx (algebra_map K₀ (integral_closure K₀ L)) 
                              (local_ring.maximal_ideal K₀) 
                              (local_ring.maximal_ideal (integral_closure K₀ L))
    ))) :=
begin
  apply ideal.quotient.algebra_quotient_of_ramification_idx_ne_zero 
    (algebra_map K₀ (integral_closure K₀ L)) _ _,
  rw ← extended_eq_pow_ramification_index,
  apply ramification_idx_extended_ne_zero,
end


/-- The quotient of the ring of integers in `L` by the extension of the maximal ideal in `K₀` as an
algebra over the residue field of `K₀`-/
@[reducible]
def algebra_mod_extended : algebra (residue_field K₀)
  ((integral_closure K₀ L) ⧸ (extended_max_ideal K L)) :=
begin
  rw [extended_eq_pow_ramification_index],
  apply_instance,
end


lemma algebra_map_comp_extended : (@algebra_map (residue_field K₀)
    ((integral_closure K₀ L) ⧸ (local_ring.maximal_ideal (integral_closure K₀ L) ^ 
    (ramification_idx (algebra_map K₀ (integral_closure K₀ L)) 
                              (local_ring.maximal_ideal K₀) 
                              (local_ring.maximal_ideal (integral_closure K₀ L)))))
  _ _ _) ∘ (ideal.quotient.mk (local_ring.maximal_ideal K₀)) =
  ideal.quotient.mk ((local_ring.maximal_ideal (integral_closure K₀ L) ^ 
    (ramification_idx (algebra_map K₀ (integral_closure K₀ L)) 
                              (local_ring.maximal_ideal K₀) 
                              (local_ring.maximal_ideal (integral_closure K₀ L)))))
  ∘ (algebra_map K₀ (integral_closure K₀ L)) := rfl

lemma algebra_map_comp_power_e : (@algebra_map (residue_field K₀)
    ((integral_closure K₀ L) ⧸ (extended_max_ideal K L))
      _ _ (algebra_mod_extended K L)) ∘ (ideal.quotient.mk (local_ring.maximal_ideal K₀)) =
  ideal.quotient.mk (extended_max_ideal K L) ∘ (algebra_map K₀ (integral_closure K₀ L)) :=
begin
  convert (algebra_map_comp_extended K L) using 4, 
  any_goals {rw extended_eq_pow_ramification_index},
  { simp only [algebra_mod_extended],
    simp only [eq_mpr_eq_cast, ← cast_cast, cast_heq], }
end

local attribute [instance] algebra_mod_extended

lemma algebra_map_comp_power_e_apply (a : K₀) : 
  (algebra_map (residue_field K₀) ((integral_closure K₀ L) ⧸ (extended_max_ideal K L))) 
    (ideal.quotient.mk (local_ring.maximal_ideal K₀) a) =
  ideal.quotient.mk (extended_max_ideal K L) (algebra_map K₀ (integral_closure K₀ L) a) :=
begin
  have : ((algebra_map (residue_field K₀)
    ((integral_closure K₀ L) ⧸ (extended_max_ideal K L))
      ) ∘ (ideal.quotient.mk (local_ring.maximal_ideal K₀))) a =
  (ideal.quotient.mk (extended_max_ideal K L) ∘ (algebra_map K₀ (integral_closure K₀ L))) a,
  rwa algebra_map_comp_power_e
end


lemma scalar_tower_extended : is_scalar_tower K₀ (residue_field K₀)
  ((integral_closure K₀ L) ⧸ (extended_max_ideal K L)) :=
begin
  refine is_scalar_tower.of_algebra_map_eq (λ a, _),
  have algebra_map_comp : algebra_map K₀ ((integral_closure K₀ L) ⧸ (extended_max_ideal K L)) a =
    (ideal.quotient.mk (extended_max_ideal K L) ∘ (algebra_map K₀ (integral_closure K₀ L))) a,
  { refl },
  have algebra_map_eq_quot_mk : algebra_map K₀ (residue_field K₀) a =
    (ideal.quotient.mk (local_ring.maximal_ideal K₀)) a,
  { refl },
  rw [algebra_map_comp, ← algebra_map_comp_power_e, algebra_map_eq_quot_mk],
end


lemma scalar_tower_power_e : is_scalar_tower K₀ (residue_field K₀)
  ((integral_closure K₀ L) ⧸ (local_ring.maximal_ideal (integral_closure K₀ L) ^ 
    (ramification_idx (algebra_map K₀ (integral_closure K₀ L)) 
      (local_ring.maximal_ideal K₀) 
      (local_ring.maximal_ideal (integral_closure K₀ L))))) :=
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
                              (local_ring.maximal_ideal (integral_closure K₀ L))))) ∘ 
      (algebra_map K₀ (integral_closure K₀ L))) a,
  { refl },
  have algebra_map_eq_quot_mk : algebra_map K₀ (residue_field K₀) a =
    (ideal.quotient.mk (local_ring.maximal_ideal K₀)) a,
  refl,
  rw [algebra_map_comp, ← algebra_map_comp_extended, algebra_map_eq_quot_mk],
end

/-- The equivalence as vector spaces over the residue field of the base of
* the quotient of the integral closure of `K₀` modulo the extension of the maximal ideal below; and
* the quotient of the integral closure of `K₀` modulo the `e`-th power of the maximal idal above;
induced by the equality of the two ideals proved in `extended_eq_pow_ramification_index` -/
noncomputable!
def quotient_linear_iso : ((integral_closure K₀ L) ⧸ (extended_max_ideal K L)) ≃ₗ[residue_field K₀]
  ((integral_closure K₀ L) ⧸ (local_ring.maximal_ideal (integral_closure K₀ L) ^ 
    (ramification_idx (algebra_map K₀ (integral_closure K₀ L)) 
                              (local_ring.maximal_ideal K₀) 
                              (local_ring.maximal_ideal (integral_closure K₀ L))))) :=
begin
  let f := (submodule.quot_equiv_of_eq _ _
    (extended_eq_pow_ramification_index K L)).restrict_scalars K₀,
  let g :
  ((integral_closure K₀ L) ⧸ (extended_max_ideal K L))
  →ₗ[residue_field K₀]
  ((integral_closure K₀ L) ⧸ (local_ring.maximal_ideal (integral_closure K₀ L) ^ 
    (ramification_idx (algebra_map K₀ (integral_closure K₀ L)) 
                              (local_ring.maximal_ideal K₀) 
                              (local_ring.maximal_ideal (integral_closure K₀ L))))),
  { use λ x, f x,
    { apply f.map_add },
    { rintros ⟨a⟩ v,
      simp only [submodule.quotient.quot_mk_eq_mk, quotient.mk_eq_mk, embedding_like.apply_eq_iff_eq],
      have algebra_map_eq_quot_mk : algebra_map K₀ (residue_field K₀) a = (ideal.quotient.mk
        (local_ring.maximal_ideal K₀)) a,
      { refl },
      let scalar_tower_v := (scalar_tower_extended K L).1 a 1 v,
      let scalar_tower_fv := (scalar_tower_power_e K L).1 a 1 (f v),
      rw [← algebra.algebra_map_eq_smul_one a, one_smul, algebra_map_eq_quot_mk] at 
        scalar_tower_v scalar_tower_fv,
      rw [scalar_tower_v, ring_hom.id_apply, scalar_tower_fv],
      apply f.map_smul  }},
  have h : function.bijective g,
  { apply f.bijective },
  use linear_equiv.of_bijective g f.bijective,
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
    ((integral_closure K₀ L) ⧸ (extended_max_ideal K L)) = finite_dimensional.finrank K L,
  { apply @finrank_quotient_map K₀ _ (integral_closure K₀ L) _ (local_ring.maximal_ideal K₀)
    _ K _ _ _ L _ _ (integral_closure.is_fraction_ring_of_finite_extension K L)
    _ _ _ _ _ _ _ _ _ _ },
  haveI : finite_dimensional (residue_field K₀)
    ((integral_closure K₀ L) ⧸ (extended_max_ideal K L)),
  { suffices : 0 < finite_dimensional.finrank K L,
    { apply finite_dimensional.finite_dimensional_of_finrank,
      convert this using 1,
      rw ← aux,
      congr' 2,
      apply algebra.algebra_ext,
      rintro ⟨a⟩,
      simp only [submodule.quotient.quot_mk_eq_mk, quotient.mk_eq_mk,
        algebra_map_comp_power_e_apply K L a, ← quotient.algebra_map_quotient_map_quotient],
      refl },
    { rw finite_dimensional.finrank_pos_iff_exists_ne_zero,
      use 1,
      apply one_ne_zero }},
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
      haveI := (quotient_linear_iso K L).finite_dimensional,
      apply (@submodule.top_equiv (residue_field K₀) 
        ((integral_closure K₀ L) ⧸ (local_ring.maximal_ideal (integral_closure K₀ L) ^ 
        (ramification_idx (algebra_map K₀ (integral_closure K₀ L)) 
                              (local_ring.maximal_ideal K₀) 
                              (local_ring.maximal_ideal (integral_closure K₀ L))
        ))) _ _ _).symm.finite_dimensional  },
    exact @finite_dimensional.finite_dimensional_quotient (residue_field K₀) _ _ _ _ aux _,
end


lemma finite_dimensional_residue_field_of_integral_closure [is_separable K L] : 
  finite_dimensional (residue_field K₀) (residue_field (integral_closure K₀ L)) :=
begin
  let alg := (algebra_residue_fields K L),
  dsimp only [residue_field] at alg,
  letI := alg,
  letI h0 := ramification_idx_maximal_ne_zero K L,
  have zero_lt : 0 < (ramification_idx (algebra_map K₀ (integral_closure K₀ L)) 
                              (local_ring.maximal_ideal K₀) 
                              (local_ring.maximal_ideal (integral_closure K₀ L))), 
  { apply nat.pos_of_ne_zero h0.1 },
  let surj := quotient_range_pow_quot_succ_inclusion_equiv (algebra_map K₀
    (integral_closure K₀ L)) (local_ring.maximal_ideal K₀)
    (local_ring.maximal_ideal (integral_closure K₀ L)) (discrete_valuation_ring.not_a_field _)
      zero_lt,
  apply @linear_equiv.finite_dimensional (residue_field K₀) _ _ _ _
    (residue_field (integral_closure K₀ L)) _ _ surj (finite_dimensional_pow K L),
end


/-- The residue field of the integral closure of a DVR in a  finite, separable extension of a
fraction field of the DVR is finite if the residue field of the base is finite-/
noncomputable!
def finite_residue_field_of_integral_closure [is_separable K L] 
  (hres : fintype (residue_field K₀)) :
  fintype (residue_field (integral_closure K₀ L)) :=
begin
  letI := finite_dimensional_residue_field_of_integral_closure K L,
  exact (module.fintype_of_fintype (finite_dimensional.fin_basis 
    (residue_field K₀) (residue_field (integral_closure K₀ L)))),
end


/-- The residue field of the unit ball of a  finite, separable extension of a fraction field of a
DVR is finite if the residue field of the base is finite-/
noncomputable!
def finite_residue_field_of_unit_ball [is_separable K L] 
  (hres : fintype (local_ring.residue_field K₀)) :
 fintype (residue_field (extended_valuation K L).valuation_subring) :=
@fintype.of_equiv _ _ (finite_residue_field_of_integral_closure K L hres) 
  (local_ring.residue_field.map_equiv
  (ring_equiv.subring_congr 
  (discrete_valuation.extension.integral_closure_eq_integer K L))).to_equiv

end discrete_valuation