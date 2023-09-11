import for_mathlib.ring_theory.valuation.algebra_instances
import padic_compare
import number_theory.padics.padic_integers
import ring_theory.dedekind_domain.integral_closure
import ring_theory.discrete_valuation_ring.basic

/-!
# Mixed characteristic local fields

In this file we define a mixed characteristic local field as a finite extension of 
the field of `p`-adic numbers, defined as the completion `Q_p` of `ℚ` with respect to the adic
valuation associated with the maximal ideal `pℤ ⊆ ℤ`. See `padic_compare.lean` for more details
about the comparison between this type and the type `ℚ_[p]` as defined in `mathlib`.

## Main Definitions
* `mixed_char_local_field` defines a mixed characteristic local field as a finite dimensional
`Q_p`-algebra for some prime number `p`, where `Q_p` is defined in `padic_compare.lean`

##  Main Theorems
* The instance of `mixed_char_local_field` on `Q_p`.
* `ring_of_integers_equiv` proves that `Z_p`, defined as the unit ball inside `Q_p` coincides with
its ring of integers when seeing `Q_p` as a mixed characteristic local field.
* `residue_field_fintype_of_completion` proves that the residue field of the ring of integers of a
mixed characteristic local field is finite.
-/

noncomputable theory

open padic padic_comparison padic_comparison.padic' discrete_valuation valuation
open_locale discrete_valuation

variables (p : ℕ) [fact(nat.prime p)] 

/-- A mixed characteristic local field is a field which has characteristic zero and is finite
dimensional over `Q_p p`, for some prime `p`. -/
class mixed_char_local_field (p : out_param(ℕ)) [fact(nat.prime p)] (K : Type*) [field K]
  extends algebra (Q_p p) K :=
[to_finite_dimensional : finite_dimensional (Q_p p) K] 

namespace mixed_char_local_field

@[priority 100, nolint dangerous_instance]
instance to_char_zero (p : out_param(ℕ)) [fact(nat.prime p)]
  (K : Type*) [field K] [mixed_char_local_field p K] : char_zero K := --infer_instance
⟨λ n m h, by rwa [← map_nat_cast (algebra_map (Q_p p) K), ← map_nat_cast (algebra_map (Q_p p) K),
  (algebra_map (Q_p p) K).injective.eq_iff, nat.cast_inj] at h⟩

attribute [priority 100, instance] to_finite_dimensional

variables (K : Type*) [field K] [mixed_char_local_field p K]
variables (L : Type*) [field L] [mixed_char_local_field p L]

protected lemma is_algebraic : algebra.is_algebraic (Q_p p) K := algebra.is_algebraic_of_finite _ _

/-- The ring of integers of a mixed characteristic local field is the integral closure of ℤ_[p]
  in the local field. -/
def ring_of_integers := integral_closure (Z_p p) K

localized "notation (name := ring_of_integers)
  `𝓞` := mixed_char_local_field.ring_of_integers" in mixed_char_local_field

lemma mem_ring_of_integers (x : K) : x ∈ 𝓞 p K ↔ is_integral (Z_p p) x := iff.rfl

lemma is_integral_of_mem_ring_of_integers {x : K} (hx : x ∈ 𝓞 p K) :
  is_integral (Z_p p) (⟨x, hx⟩ : 𝓞 p K) :=
begin
  obtain ⟨P, hPm, hP⟩ := hx,
  refine ⟨P, hPm, _⟩,
  rw [← polynomial.aeval_def, ← subalgebra.coe_eq_zero, polynomial.aeval_subalgebra_coe,
    polynomial.aeval_def,  subtype.coe_mk, hP],
end


/-- Given an algebra between two local fields over Q_p, create an algebra between their two rings
of integers. For now, this is not an instance by default as it creates an equal-but-not-defeq
diamond with `algebra.id` when `K = L`. This is caused by `x = ⟨x, x.prop⟩` not being defeq on
subtypes. It will be an instance when ported to Lean 4, since the above will not be an issue. -/
def ring_of_integers_algebra [algebra K L] [is_scalar_tower (Q_p p) K L] :
  algebra (𝓞 p K) (𝓞 p L) := 
valuation_subring.valuation_subring_algebra _ K L

namespace ring_of_integers

variables {K}


noncomputable! instance : is_fraction_ring (𝓞 p K) K := 
integral_closure.is_fraction_ring_of_finite_extension (Q_p p) _

instance : is_integral_closure (𝓞 p K) (Z_p p) K :=
integral_closure.is_integral_closure _ _


noncomputable! instance : is_integrally_closed (𝓞 p K) :=
integral_closure.is_integrally_closed_of_finite_extension (Q_p p)

lemma is_integral_coe (x : 𝓞 p K) : is_integral (Z_p p) (x : K) := x.2

/-- The ring of integers of `K` is equivalent to any integral closure of `Z_p` in `K` -/
protected noncomputable! def equiv (R : Type*) [comm_ring R] [algebra (Z_p p) R] [algebra R K]
  [is_scalar_tower (Z_p p) R K] [is_integral_closure R (Z_p p) K] : 𝓞 p K ≃+* R := 
valuation_subring.equiv _ K R

variables (K)

instance : char_zero (𝓞 p K) := char_zero.of_module _ K

instance : is_noetherian (Z_p p) (𝓞 p K) :=
is_integral_closure.is_noetherian (Z_p p) (Q_p p) K (𝓞 p K)

lemma algebra_map_injective :
  function.injective ⇑(algebra_map (Z_p p) (ring_of_integers p K)) := 
valuation_subring.integral_closure_algebra_map_injective _ K

end ring_of_integers

end mixed_char_local_field

namespace padic

open mixed_char_local_field

instance mixed_char_local_field (p : ℕ) [fact(nat.prime p)] : mixed_char_local_field p (Q_p p) :=
{ to_finite_dimensional := infer_instance }

/-- The ring of integers of `Q_p p` as a mixed characteristic local field is just `Z_p`. -/
noncomputable def ring_of_integers_equiv (p : ℕ) [fact(nat.prime p)] :
  ring_of_integers p (Q_p p) ≃+* (Z_p p) :=
ring_of_integers.equiv p (Z_p p)


namespace ring_of_integers
open discrete_valuation


instance : fintype (local_ring.residue_field (Z_p p)) := 
fintype.of_equiv _ (padic_comparison.residue_field p).to_equiv.symm

/-- The `fintype` structure on the residue field of `Z_p`. -/
definition residue_field_fintype_of_completion : fintype (local_ring.residue_field (Z_p p)) := 
infer_instance

end ring_of_integers

end padic