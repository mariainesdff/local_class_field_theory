/-
Copyright (c) 2023 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import discrete_valuation_ring.extensions
import for_mathlib.padic_compare
import number_theory.padics.padic_integers
import ring_theory.dedekind_domain.integral_closure
import ring_theory.discrete_valuation_ring


-- import for_mathlib.algebra_comp

/-!
--TODO: Fix comments
# Mixed characteristic local fields
This file defines a number field, the ring of integers corresponding to it and includes some
basic facts about the embeddings into an algebraic closed field.
## Main definitions
 - `mixed_char_local_field` defines a number field as a field which has characteristic zero and is
    finite dimensional over ℚ.
 - `ring_of_integers` defines the ring of integers (or number ring) corresponding to a number field
    as the integral closure of ℤ in the number field.
## Main Result
 - `eq_roots`: let `x ∈ K` with `K` number field and let `A` be an algebraic closed field of
    char. 0, then the images of `x` by the embeddings of `K` in `A` are exactly the roots in
    `A` of the minimal polynomial of `x` over `ℚ`.
## Implementation notes
The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice.
## References
* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Fröhlich, *Algebraic Number Theory*][cassels1967algebraic]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1970algebraic]
## Tags
number field, ring of integers
-/

noncomputable theory

-- For instances and lemmas that only need `K` to be a `ℚₚ`-algebra
-- namespace padic_algebra 

open padic padic' discrete_valuation valuation
open_locale discrete_valuation

variables (p : ℕ) [fact(nat.prime p)] 

-- (K L : Type*) [field K] [hK : algebra (Q_p p) K] [field L]
--   [algebra (Q_p p) L]

-- include hK/

-- instance to_int_algebra : algebra (Z_p p) K := infer_instance --algebra.comp (Z_p p) (Q_p p) K

-- @[simp] lemma int_algebra_map_def : algebra_map ℤ_[p] K = 
--   (padic_algebra.to_int_algebra p K).to_ring_hom := rfl 

-- @[priority 10000] instance [is_discrete (@valued.v (Q_p p) _ ℤₘ₀ _ _)] : is_scalar_tower (Z_p p) (Q_p p) K :=
-- infer_instance--discrete_valuation.is_scalar_tower (Q_p p) K

-- @[priority 1000] instance int_is_scalar_tower [is_discrete (@valued.v (Q_p p) _ ℤₘ₀ _ _)]
-- [algebra K L] [is_scalar_tower (Q_p p) K L] :
--   is_scalar_tower (Z_p p) K L := infer_instance
-- is_scalar_tower.comp' ℤ_[p] ℚ_[p] K L

-- omit hK

--`


-- lemma algebra_map_injective {E : Type*} [field E] [algebra (Q_p p) E]
--   [is_scalar_tower (Z_p p) (Q_p p) E] [is_discrete (@valued.v (Q_p p) _ ℤₘ₀ _ _)] :
--   function.injective ⇑(algebra_map (Z_p p) E) :=
-- begin
--   exact discrete_valuation.algebra_map_injective (Q_p p) E,
-- end

-- end padic_algebra

-- include p

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

-- We need to mark this one with high priority to avoid timeouts.
-- @[priority 10000] instance : is_scalar_tower ℤ_[p] ℚ_[p] K := infer_instance

protected lemma is_algebraic : algebra.is_algebraic (Q_p p) K := algebra.is_algebraic_of_finite _ _

/-- The ring of integers of a mixed characteristic local field is the integral closure of ℤ_[p]
  in the local field. -/
def ring_of_integers := integral_closure (Z_p p) K

localized "notation (name := ring_of_integers)
  `𝓞` := mixed_char_local_field.ring_of_integers" in mixed_char_local_field

lemma mem_ring_of_integers (x : K) : x ∈ 𝓞 p K ↔ is_integral (Z_p p) x := iff.rfl

--TODO: Might need to delete if lean can use the one in `dvr_extensions`
lemma is_integral_of_mem_ring_of_integers {x : K} (hx : x ∈ 𝓞 p K) :
  is_integral (Z_p p) (⟨x, hx⟩ : 𝓞 p K) :=
begin
  obtain ⟨P, hPm, hP⟩ := hx,
  refine ⟨P, hPm, _⟩,
  rw [← polynomial.aeval_def, ← subalgebra.coe_eq_zero, polynomial.aeval_subalgebra_coe,
    polynomial.aeval_def,  subtype.coe_mk, hP],
end

--TODO: Might need to delete if lean can use the one in `dvr_extensions`; also, need to delete the
-- assumption on the valuation being discrete

/-- Given an algebra between two local fields over ℚ_[p], create an algebra between their two rings
of integers. For now, this is not an instance by default as it creates an equal-but-not-defeq
diamond with `algebra.id` when `K = L`. This is caused by `x = ⟨x, x.prop⟩` not being defeq on
subtypes. This will likely change in Lean 4. -/
def ring_of_integers_algebra [algebra K L] [is_scalar_tower (Q_p p) K L]
  : algebra (𝓞 p K) (𝓞 p L) := sorry
-- ring_hom.to_algebra
-- { to_fun := λ k, ⟨algebra_map K L k, is_integral.algebra_map k.2⟩,
--   map_zero' := subtype.ext $ by simp only [subtype.coe_mk, subalgebra.coe_zero, map_zero],
--   map_one'  := subtype.ext $ by simp only [subtype.coe_mk, subalgebra.coe_one, map_one],
--   map_add'  := λ x y, subtype.ext $ by simp only [map_add, subalgebra.coe_add, subtype.coe_mk],
--   map_mul'  := λ x y, subtype.ext $ by simp only [subalgebra.coe_mul, map_mul, subtype.coe_mk] }

namespace ring_of_integers

variables {K}

--set_option profiler true 
-- Takes 2.62 s
--set_option trace.class_instances true
-- I had to increase the priority of `mixed_char_local_field.is_scalar_tower` for this to work.
-- Otherwise it times out if the is_scalar_tower argument is implicit
noncomputable! instance : is_fraction_ring (𝓞 p K) K := 
integral_closure.is_fraction_ring_of_finite_extension (Q_p p) _

instance : is_integral_closure (𝓞 p K) (Z_p p) K :=
integral_closure.is_integral_closure _ _

--set_option profiler true
-- Takes 3.29 s
-- Times out if the is_scalar_tower argument is implicit (without the priority fix)
noncomputable! instance : is_integrally_closed (𝓞 p K) :=
integral_closure.is_integrally_closed_of_finite_extension (Q_p p)

lemma is_integral_coe (x : 𝓞 p K) : is_integral (Z_p p) (x : K) := x.2

--TODO: It has been generalized
/-- The ring of integers of `K` is equivalent to any integral closure of `ℤ_[p]` in `K` -/

protected noncomputable! def equiv (R : Type*) [comm_ring R] [algebra (Z_p p) R] [algebra R K]
  [is_scalar_tower (Z_p p) R K] [is_integral_closure R (Z_p p) K] : 𝓞 p K ≃+* R := sorry
-- (is_integral_closure.equiv ℤ_[p] R K _).symm.to_ring_equiv

variables (K)

instance : char_zero (𝓞 p K) := char_zero.of_module _ K

-- noncomputable! instance : is_noetherian (Z_p p) (𝓞 p K) :=
-- is_integral_closure.is_noetherian (Z_p p) (Z_p p) K (𝓞 p K)


-- `TODO` Can probably remove, it is in `dvr_extension`
noncomputable! lemma algebra_map_injective :
  function.injective ⇑(algebra_map (Z_p p) (ring_of_integers p K)) := 
begin
  have hinj : function.injective ⇑(algebra_map (Z_p p) K),
  { exact algebra_map_injective (Q_p p) K},
  rw injective_iff_map_eq_zero (algebra_map (Z_p p) ↥(𝓞 p K)),
  intros x hx,
  rw [← subtype.coe_inj, subalgebra.coe_zero] at hx,
  rw injective_iff_map_eq_zero (algebra_map (Z_p p) K) at hinj,
  exact hinj x hx, 
end

end ring_of_integers

end mixed_char_local_field

namespace padic

open mixed_char_local_field

instance mixed_char_local_field (p : ℕ) [fact(nat.prime p)] : mixed_char_local_field p (Q_p p) :=
{ to_finite_dimensional := infer_instance}
--   infer_instance,
  -- The vector space structure of `ℚ` over itself can arise in multiple ways:
  -- all fields are vector spaces over themselves (used in `rat.finite_dimensional`)
  -- all char 0 fields have a canonical embedding of `ℚ` (used in `mixed_char_local_field`).
  -- Show that these coincide:
  -- by convert (infer_instance : finite_dimensional (Q_p p) (Q_p p)), 
  -- }

--`TODO`: Seems long!
/-- The ring of integers of `Q_p p` as a mixed characteristic local field is just `Z_p p`. -/
noncomputable def ring_of_integers_equiv (p : ℕ) [fact(nat.prime p)] :
  ring_of_integers p (Q_p p) ≃+* (Z_p p) :=
ring_of_integers.equiv p (Z_p p)

end padic