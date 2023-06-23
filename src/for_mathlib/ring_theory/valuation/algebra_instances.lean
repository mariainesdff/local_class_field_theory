import algebra.order.group.type_tags
import ring_theory.valuation.valuation_subring

open function valuation

open_locale discrete_valuation

variables {K : Type*} [field K] (v : valuation K ℤₘ₀) (L : Type*) [field L] [algebra K L]

namespace valuation_subring

instance algebra' : algebra v.valuation_subring L := 
algebra.of_subring v.valuation_subring.to_subring

@[simp] lemma algebra_map_def : algebra_map v.valuation_subring L = 
  (valuation_subring.algebra' v L).to_ring_hom := rfl 

/- @[priority 10000]  -/instance : is_scalar_tower v.valuation_subring K L :=
is_scalar_tower.subsemiring v.valuation_subring.to_subsemiring

lemma algebra_map_injective : 
  injective (algebra_map v.valuation_subring L) :=
injective.comp (algebra_map K L).injective (is_fraction_ring.injective v.valuation_subring K)

lemma is_integral_of_mem_ring_of_integers {x : L} 
  (hx : x ∈ integral_closure v.valuation_subring L) :
  is_integral v.valuation_subring (⟨x, hx⟩ : integral_closure v.valuation_subring L) :=
begin
  obtain ⟨P, hPm, hP⟩ := hx,
  refine ⟨P, hPm, _⟩,
  rw [← polynomial.aeval_def, ← subalgebra.coe_eq_zero, polynomial.aeval_subalgebra_coe,
    polynomial.aeval_def,  subtype.coe_mk, hP],
end

variables (E : Type*) [field E] [algebra K E] [algebra L E] [is_scalar_tower K L E] 

/- @[priority 1000]  -/instance int_is_scalar_tower :
  is_scalar_tower v.valuation_subring L E :=
{ smul_assoc := λ x y z,
  begin
    nth_rewrite 0 [← one_smul K y],
    rw [← one_smul K (y • z), ← smul_assoc, ← smul_assoc, ← smul_assoc],
  end }

/-- Given an algebra between two local fields over 𝔽_[p]⟮⟮X⟯⟯, create an algebra between their two
  rings of integers. For now, this is not an instance by default as it creates an
  equal-but-not-defeq diamond with `algebra.id` when `K = L`. This is caused by `x = ⟨x, x.prop⟩`
  not being defeq on subtypes. This will likely change in Lean 4. -/
def valuation_subring_algebra :
  algebra (integral_closure v.valuation_subring L) (integral_closure v.valuation_subring E) := 
ring_hom.to_algebra
{ to_fun := λ k, ⟨algebra_map L E k, is_integral.algebra_map k.2⟩,
  map_zero' := subtype.ext $ by simp only [subtype.coe_mk, subalgebra.coe_zero, _root_.map_zero],
  map_one'  := subtype.ext $ by simp only [subtype.coe_mk, subalgebra.coe_one,  _root_.map_one],
  map_add'  := λ x y, subtype.ext $ 
    by simp only [ _root_.map_add, subalgebra.coe_add, subtype.coe_mk],
  map_mul'  := λ x y, subtype.ext $ 
    by simp only [subalgebra.coe_mul,  _root_.map_mul, subtype.coe_mk] }

protected noncomputable def equiv (R : Type*) [comm_ring R] [algebra v.valuation_subring R] 
  [algebra R L] [is_scalar_tower v.valuation_subring R L] 
  [is_integral_closure R v.valuation_subring L] : 
  integral_closure v.valuation_subring L ≃+* R :=
(is_integral_closure.equiv v.valuation_subring R L 
  (integral_closure v.valuation_subring L)).symm.to_ring_equiv

lemma integral_closure_algebra_map_injective : 
  injective (algebra_map v.valuation_subring (integral_closure v.valuation_subring L)) := 
begin
  have hinj : injective ⇑(algebra_map v.valuation_subring L),
  { exact valuation_subring.algebra_map_injective v L},
  rw injective_iff_map_eq_zero (algebra_map v.valuation_subring
    ↥(integral_closure v.valuation_subring L)),
  intros x hx,
  rw [← subtype.coe_inj, subalgebra.coe_zero] at hx,
  rw injective_iff_map_eq_zero (algebra_map v.valuation_subring L) at hinj,
  exact hinj x hx, 
end

end valuation_subring