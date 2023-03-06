/-
Copyright (c) 2022 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import algebra.char_p.subring

import field_theory.finite.galois_field
import ring_theory.dedekind_domain.adic_valuation
import ring_theory.dedekind_domain.integral_closure

import ring_theory.laurent_series

import algebra_comp
import for_mathlib.polynomial

/-!
--TODO: Fix comments
# Mixed characteristic local fields fields
This file defines a number field, the ring of integers corresponding to it and includes some
basic facts about the embeddings into an algebraic closed field.
## Main definitions
 - `eq_char_local_field` defines a number field as a field which has characteristic zero and is
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

open_locale discrete_valuation
open polynomial multiplicative ratfunc

variables (p : ℕ) [fact(nat.prime p)] 

notation (name := prime_galois_field)
  `𝔽_[` p `]` := galois_field p 1

/- The valued field `Fp(X)` with the valuation at `X`. -/
def FpX_valued  : valued (ratfunc 𝔽_[p]) ℤₘ₀ :=
valued.mk' (ideal_X 𝔽_[p]).valuation

lemma FqX_valued_def {x : ratfunc 𝔽_[p]} :
  @valued.v (ratfunc 𝔽_[p]) _ _ _ (FpX_valued p) x = (ideal_X 𝔽_[p]).valuation x := rfl 

def FpX_field_completion  :=
 (ideal_X 𝔽_[p]).adic_completion (ratfunc 𝔽_[p])

notation (name := FpX_field_completion)
  `𝔽_[` p `]⟮⟮` X `⟯⟯` := FpX_field_completion p

def FpX_int_completion  :=
 (ideal_X 𝔽_[p]).adic_completion_integers (ratfunc 𝔽_[p])

notation (name := FpX_int_completion)
  `𝔽_[` p `]⟦` X `⟧` := FpX_int_completion p

variable {p}

instance : field 𝔽_[p]⟮⟮X⟯⟯ :=  --sorry
is_dedekind_domain.height_one_spectrum.adic_completion.field (ratfunc 𝔽_[p]) (ideal_X 𝔽_[p])

instance : inhabited 𝔽_[p]⟮⟮X⟯⟯ := ⟨(0 : 𝔽_[p]⟮⟮X⟯⟯)⟩

-- Upgrade to (ratfunc Fp)-algebra iso
noncomputable!
def isom_laurent : 𝔽_[p]⟮⟮X⟯⟯  ≃+* (laurent_series 𝔽_[p]) := sorry -- F


-- Upgrade to (ratfunc Fp)-algebra iso
noncomputable! def isom_power_series : 𝔽_[p]⟦X⟧  ≃+* (power_series 𝔽_[p]) := sorry -- F

instance : algebra 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯ :=
(by apply_instance : algebra ((ideal_X 𝔽_[p]).adic_completion_integers (ratfunc 𝔽_[p]))
  ((ideal_X 𝔽_[p]).adic_completion (ratfunc 𝔽_[p])))

noncomputable! instance : is_fraction_ring 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯ :=
(by apply_instance : is_fraction_ring ((ideal_X 𝔽_[p]).adic_completion_integers (ratfunc 𝔽_[p]))
  ((ideal_X 𝔽_[p]).adic_completion (ratfunc 𝔽_[p])))

-- For instances and lemmas that only need `K` to be an `𝔽_[p]⟮⟮X⟯⟯`-algebra
namespace adic_algebra

variables (K L : Type*) [field K] [algebra 𝔽_[p]⟮⟮X⟯⟯ K] [field L]
  [algebra 𝔽_[p]⟮⟮X⟯⟯ L]

instance to_int_algebra : algebra 𝔽_[p]⟦X⟧ K := algebra.comp 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯ K
--(ring_hom.comp (algebra_map 𝔽_[p]⟮⟮X⟯⟯ K) (algebra_map 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯)).to_algebra

@[simp] lemma int_algebra_map_def : algebra_map 𝔽_[p]⟦X⟧ K = 
  (adic_algebra.to_int_algebra K).to_ring_hom := rfl 

@[priority 10000] instance : is_scalar_tower 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯ K :=
is_scalar_tower.comp 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯ K
/- ⟨λ _ _ _, by simp only [algebra.smul_def, int_algebra_map_def, map_mul, ← mul_assoc]; refl⟩ -/

@[priority 1000] instance int_is_scalar_tower [algebra K L] [is_scalar_tower 𝔽_[p]⟮⟮X⟯⟯ K L] :
  is_scalar_tower 𝔽_[p]⟦X⟧ K L :=
is_scalar_tower.comp' 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯ K L

/- { smul_assoc := λ x y z,
  begin
    nth_rewrite 0 [← one_smul 𝔽_[p]⟮⟮X⟯⟯ y],
    rw [← one_smul 𝔽_[p]⟮⟮X⟯⟯ (y • z), ← smul_assoc, ← smul_assoc, ← smul_assoc],
  end } -/

lemma algebra_map_injective {E : Type*} [field E] [algebra 𝔽_[p]⟦X⟧ E] [algebra 𝔽_[p]⟮⟮X⟯⟯ E]
  [is_scalar_tower 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯ E] : function.injective ⇑(algebra_map 𝔽_[p]⟦X⟧ E) :=
algebra_map_injective' 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯ E
end adic_algebra



/-- An equal characteristic local field is a field which is finite
dimensional over `𝔽_p((X))`, for some prime `p`. -/
class eq_char_local_field (p : out_param(ℕ)) [fact(nat.prime p)] (K : Type*) [field K] 
  extends algebra 𝔽_[p]⟮⟮X⟯⟯ K :=
[to_finite_dimensional : finite_dimensional 𝔽_[p]⟮⟮X⟯⟯ K]


attribute [priority 100, instance] eq_char_local_field.to_finite_dimensional

namespace eq_char_local_field

variables (p) (K L : Type*) [field K] [eq_char_local_field p K] [field L] [eq_char_local_field p L]


-- We need to mark this one with high priority to avoid timeouts. (TODO: Check)
@[priority 10000] instance : is_scalar_tower 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯ K := infer_instance

-- Why protected?
/- protected  -/lemma is_algebraic : algebra.is_algebraic 𝔽_[p]⟮⟮X⟯⟯ K := algebra.is_algebraic_of_finite _ _

/-- The ring of integers of a mixed characteristic local field is the integral closure of ℤ_[p]
  in the local field. -/
def ring_of_integers := integral_closure 𝔽_[p]⟦X⟧ K


localized "notation (name := ring_of_integers)
  `𝓞` := eq_char_local_field.ring_of_integers" in eq_char_local_field

lemma mem_ring_of_integers (x : K) : x ∈ 𝓞 p K ↔ is_integral 𝔽_[p]⟦X⟧ x := iff.rfl

-- Same proof as in mixed char case
lemma is_integral_of_mem_ring_of_integers {x : K} (hx : x ∈ 𝓞 p K) :
  is_integral 𝔽_[p]⟦X⟧ (⟨x, hx⟩ : 𝓞 p K) :=
begin
  obtain ⟨P, hPm, hP⟩ := hx,
  refine ⟨P, hPm, _⟩,
  rw [← polynomial.aeval_def, ← subalgebra.coe_eq_zero, polynomial.aeval_subalgebra_coe,
    polynomial.aeval_def,  subtype.coe_mk, hP],
end


-- Same proof as in mixed char case
/-- Given an algebra between two local fields over 𝔽_[p]⟮⟮X⟯⟯, create an algebra between their two
  rings of integers. For now, this is not an instance by default as it creates an
  equal-but-not-defeq diamond with `algebra.id` when `K = L`. This is caused by `x = ⟨x, x.prop⟩`
  not being defeq on subtypes. This will likely change in Lean 4. -/
def ring_of_integers_algebra [algebra K L] [is_scalar_tower 𝔽_[p]⟮⟮X⟯⟯ K L] :
  algebra (𝓞 p K) (𝓞 p L) := 
ring_hom.to_algebra
{ to_fun := λ k, ⟨algebra_map K L k, is_integral.algebra_map k.2⟩,
  map_zero' := subtype.ext $ by simp only [subtype.coe_mk, subalgebra.coe_zero, map_zero],
  map_one'  := subtype.ext $ by simp only [subtype.coe_mk, subalgebra.coe_one, map_one],
  map_add'  := λ x y, subtype.ext $ by simp only [map_add, subalgebra.coe_add, subtype.coe_mk],
  map_mul'  := λ x y, subtype.ext $ by simp only [subalgebra.coe_mul, map_mul, subtype.coe_mk] }


namespace ring_of_integers

variables {K}

--set_option profiler true
--set_option trace.class_instances true
-- I had to increase the priority of `eq_char_local_field.is_scalar_tower` for this to work.
-- Otherwise it times out if the is_scalar_tower argument is implicit (TODO: check)
noncomputable! instance : is_fraction_ring (𝓞 p K) K := 
sorry --integral_closure.is_fraction_ring_of_finite_extension 𝔽_[p]⟮⟮X⟯⟯ K 
--This takes about 7s, I think it should be faster...


instance : is_integral_closure (𝓞 p K) 𝔽_[p]⟦X⟧ K :=
integral_closure.is_integral_closure _ _

-- Very slow too (9.37s)
--set_option profiler true
-- Times out if the is_scalar_tower argument is implicit (without the priority fix) (TODO: check)
noncomputable! instance : is_integrally_closed (𝓞 p K) :=
sorry --integral_closure.is_integrally_closed_of_finite_extension 𝔽_[p]⟮⟮X⟯⟯

lemma is_integral_coe (x : 𝓞 p K) : is_integral 𝔽_[p]⟦X⟧  (x : K) := x.2

-- 2.81 s
/-- The ring of integers of `K` is equivalent to any integral closure of `𝔽_[p]⟦X⟧` in `K` -/
protected noncomputable! def equiv (R : Type*) [comm_ring R] [algebra 𝔽_[p]⟦X⟧ R] [algebra R K]
  [is_scalar_tower 𝔽_[p]⟦X⟧ R K] [is_integral_closure R 𝔽_[p]⟦X⟧ K] : 𝓞 p K ≃+* R :=
sorry --(is_integral_closure.equiv 𝔽_[p]⟦X⟧ R K _).symm.to_ring_equiv

. 

variables (K)

instance ratfunc.char_p : char_p (ratfunc 𝔽_[p]) p := sorry

noncomputable! instance : algebra (ratfunc 𝔽_[p]) 𝔽_[p]⟮⟮X⟯⟯ := sorry

instance FpX_field_completion.char_p : char_p 𝔽_[p]⟮⟮X⟯⟯ p := 
char_p_of_injective_algebra_map
  ((algebra_map (ratfunc (galois_field p 1)) (FpX_field_completion p)).injective) p


instance eq_char_local_field.char_p : char_p K p := 
char_p_of_injective_algebra_map (algebra_map 𝔽_[p]⟮⟮X⟯⟯ K).injective p

instance : char_p (𝓞 p K) p := char_p.subring' K p (𝓞 p K).to_subring --char_zero.of_module _ K

 -- ?
noncomputable! instance : is_separable 𝔽_[p]⟮⟮X⟯⟯ K := sorry

noncomputable! instance : is_noetherian_ring ↥(FpX_int_completion p) := sorry

--timeout
noncomputable! instance : is_noetherian 𝔽_[p]⟦X⟧ (𝓞 p K) :=
sorry --is_integral_closure.is_noetherian 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯ K (𝓞 p K)

-- Same proof skeleton
noncomputable! lemma algebra_map_injective :
  function.injective ⇑(algebra_map 𝔽_[p]⟦X⟧ (ring_of_integers p K)) := 
begin
  have hinj : function.injective ⇑(algebra_map 𝔽_[p]⟦X⟧ K),
  { exact algebra_map_injective' 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯ K},
  rw injective_iff_map_eq_zero (algebra_map 𝔽_[p]⟦X⟧ ↥(𝓞 p K)),
  intros x hx,
  rw [← subtype.coe_inj, subalgebra.coe_zero] at hx,
  rw injective_iff_map_eq_zero (algebra_map 𝔽_[p]⟦X⟧ K) at hinj,
  exact hinj x hx, 
end

/-- The ring of integers of a mixed characteristic local field is not a field. -/
lemma not_is_field : ¬ is_field (𝓞 p K) :=
sorry -- TODO
/- by simpa [← (is_integral_closure.is_integral_algebra 𝔽_[p]⟦X⟧ K).is_field_iff_is_field
  (algebra_map_injective p K)] using (padic_int.not_is_field p) -/

instance : is_dedekind_domain ↥(FpX_int_completion p) := sorry

noncomputable! instance : is_dedekind_domain (𝓞 p K) :=
is_integral_closure.is_dedekind_domain 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯ K _

-- TODO : ring of integers is local
noncomputable!  instance : local_ring (𝓞 p K) :=
{ exists_pair_ne := ⟨0, 1, zero_ne_one⟩,
  is_unit_or_is_unit_of_add_one := λ a b hab,
  begin
    by_cases ha : is_unit a,
    { exact or.inl ha, },
    { right, sorry }
  end }


end ring_of_integers

end eq_char_local_field

namespace FpX_completion

open eq_char_local_field

-- TODO: change comment
instance mixed_char_local_field (p : ℕ) [fact(nat.prime p)] : 
  eq_char_local_field p 𝔽_[p]⟮⟮X⟯⟯ :=
{ to_finite_dimensional :=
  -- The vector space structure of `ℚ` over itself can arise in multiple ways:
  -- all fields are vector spaces over themselves (used in `rat.finite_dimensional`)
  -- all char 0 fields have a canonical embedding of `ℚ` (used in `mixed_char_local_field`).
  -- Show that these coincide:
  by convert (infer_instance : finite_dimensional 𝔽_[p]⟮⟮X⟯⟯ 𝔽_[p]⟮⟮X⟯⟯), }

/-- The ring of integers of `𝔽_[p]⟮⟮X⟯⟯` as a mixed characteristic local field is just `𝔽_[p]⟦X⟧`. -/
noncomputable! def ring_of_integers_equiv (p : ℕ) [fact(nat.prime p)] :
  ring_of_integers p 𝔽_[p]⟮⟮X⟯⟯ ≃+* 𝔽_[p]⟦X⟧ :=
sorry --ring_of_integers.equiv p 𝔽_[p]⟦X⟧ --timeout


end FpX_completion