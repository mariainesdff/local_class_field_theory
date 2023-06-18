/-
Copyright (c) 2023 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import algebra.char_p.subring
import discrete_valuation_ring.basic
import discrete_valuation_ring.complete
import field_theory.finite.galois_field
import ring_theory.dedekind_domain.adic_valuation
import ring_theory.dedekind_domain.integral_closure

import for_mathlib.laurent_series_iso.power_series_adic_completion

import ring_theory.laurent_series

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
open polynomial multiplicative ratfunc is_dedekind_domain is_dedekind_domain.height_one_spectrum
variables (p : ℕ) [fact(nat.prime p)] 

notation (name := prime_galois_field)
  `𝔽_[` p `]` := galois_field p 1

def FpX_field_completion :=
 (ideal_X 𝔽_[p]).adic_completion (ratfunc 𝔽_[p])

notation (name := FpX_field_completion)
  `𝔽_[` p `]⟮⟮` X `⟯⟯` := FpX_field_completion p

def FpX_int_completion :=
(ideal_X 𝔽_[p]).adic_completion_integers (ratfunc 𝔽_[p])

notation (name := FpX_int_completion)
  `𝔽_[` p `]⟦` X `⟧` := FpX_int_completion p

instance ratfunc.char_p : char_p (ratfunc 𝔽_[p]) p := 
char_p_of_injective_algebra_map ((algebra_map 𝔽_[p] (ratfunc 𝔽_[p])).injective) p

namespace FpX_field_completion

variable {p}

instance : field 𝔽_[p]⟮⟮X⟯⟯ := adic_completion.field (ratfunc 𝔽_[p]) (ideal_X 𝔽_[p])

instance : algebra (ratfunc 𝔽_[p]) 𝔽_[p]⟮⟮X⟯⟯ := 
height_one_spectrum.adic_completion.algebra _ (ratfunc 𝔽_[p]) _

instance : has_coe (ratfunc 𝔽_[p]) 𝔽_[p]⟮⟮X⟯⟯ := ⟨algebra_map (ratfunc 𝔽_[p]) 𝔽_[p]⟮⟮X⟯⟯⟩

lemma algebra_map_eq_coe (f : ratfunc 𝔽_[p]) : 
  algebra_map (ratfunc 𝔽_[p]) 𝔽_[p]⟮⟮X⟯⟯ f = coe f := rfl

instance FpX_field_completion.char_p : char_p 𝔽_[p]⟮⟮X⟯⟯ p := 
char_p_of_injective_algebra_map ((algebra_map (ratfunc (galois_field p 1)) 𝔽_[p]⟮⟮X⟯⟯).injective) p 

instance : valued 𝔽_[p]⟮⟮X⟯⟯ ℤₘ₀ := 
height_one_spectrum.valued_adic_completion (ratfunc 𝔽_[p]) (ideal_X 𝔽_[p])

instance : complete_space 𝔽_[p]⟮⟮X⟯⟯ :=
height_one_spectrum.adic_completion_complete_space (ratfunc 𝔽_[p]) (ideal_X 𝔽_[p])

lemma valuation_X :
  valued.v ((algebra_map (ratfunc (galois_field p 1)) 𝔽_[p]⟮⟮X⟯⟯) X) =
    multiplicative.of_add (-1 : ℤ) :=
begin
  rw [valued_adic_completion_def],
  erw [FpX_field_completion.algebra_map_eq_coe, valued.extension_extends, val_X_eq_one],
end

lemma mem_FpX_int_completion {x : 𝔽_[p]⟮⟮X⟯⟯} : x ∈ 𝔽_[p]⟦X⟧ ↔ (valued.v x : ℤₘ₀) ≤ 1 := iff.rfl

instance : inhabited 𝔽_[p]⟮⟮X⟯⟯ := ⟨(0 : 𝔽_[p]⟮⟮X⟯⟯)⟩

lemma X_mem_FpX_int_completion : algebra_map (ratfunc 𝔽_[p]) _ X ∈ 𝔽_[p]⟦X⟧ :=
begin
  erw [FpX_field_completion.mem_FpX_int_completion, FpX_field_completion.valuation_X],
  rw [← with_zero.coe_one, with_zero.coe_le_coe, ← of_add_zero, of_add_le],
  linarith,
end

variable (p)
-- Upgrade to (ratfunc Fp)-algebra iso
def isom_laurent : 𝔽_[p]⟮⟮X⟯⟯  ≃+* (laurent_series 𝔽_[p]) := 
completion_laurent_series.laurent_series_ring_equiv 𝔽_[p]

end FpX_field_completion

namespace FpX_int_completion

-- Upgrade to (ratfunc Fp)-algebra iso
noncomputable! def isom_power_series : 𝔽_[p]⟦X⟧  ≃+* (power_series 𝔽_[p]) := sorry -- F

variable {p}

instance : discrete_valuation_ring 𝔽_[p]⟦X⟧ := discrete_valuation.dvr_of_is_discrete _

instance : algebra 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯ :=
(by apply_instance : algebra ((ideal_X 𝔽_[p]).adic_completion_integers (ratfunc 𝔽_[p]))
  ((ideal_X 𝔽_[p]).adic_completion (ratfunc 𝔽_[p])))

instance : has_coe 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯ := ⟨algebra_map _ _⟩

lemma algebra_map_eq_coe (x : 𝔽_[p]⟦X⟧) : algebra_map 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯ x = x := rfl

instance is_fraction_ring : is_fraction_ring 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯ :=
(by apply_instance : is_fraction_ring ((ideal_X 𝔽_[p]).adic_completion_integers (ratfunc 𝔽_[p]))
  ((ideal_X 𝔽_[p]).adic_completion (ratfunc 𝔽_[p])))

variable (p)
instance : is_integral_closure 𝔽_[p]⟦X⟧ 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯ := 
is_integrally_closed.is_integral_closure

def X : 𝔽_[p]⟦X⟧ := ⟨algebra_map (ratfunc 𝔽_[p]) _ X, FpX_field_completion.X_mem_FpX_int_completion⟩

end FpX_int_completion

-- For instances and lemmas that only need `K` to be an `𝔽_[p]⟮⟮X⟯⟯`-algebra
namespace adic_algebra

variables {p} (K L : Type*) [field K] [algebra 𝔽_[p]⟮⟮X⟯⟯ K] [field L] [algebra 𝔽_[p]⟮⟮X⟯⟯ L]

instance to_int_algebra : algebra 𝔽_[p]⟦X⟧ K := algebra.comp 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯ K

@[simp] lemma int_algebra_map_def : algebra_map 𝔽_[p]⟦X⟧ K = 
  (adic_algebra.to_int_algebra K).to_ring_hom := rfl 

@[priority 10000] instance : is_scalar_tower 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯ K :=
is_scalar_tower.comp 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯ K

@[priority 1000] instance int_is_scalar_tower [algebra K L] [is_scalar_tower 𝔽_[p]⟮⟮X⟯⟯ K L] :
  is_scalar_tower 𝔽_[p]⟦X⟧ K L :=
is_scalar_tower.comp' 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯ K L

lemma algebra_map_injective {E : Type*} [field E] [algebra 𝔽_[p]⟦X⟧ E] [algebra 𝔽_[p]⟮⟮X⟯⟯ E]
  [is_scalar_tower 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯ E] : function.injective ⇑(algebra_map 𝔽_[p]⟦X⟧ E) :=
algebra_map_injective' 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯ E

end adic_algebra

variable (p)
/-- An equal characteristic local field is a field which is finite
dimensional over `𝔽_p((X))`, for some prime `p`. -/
class eq_char_local_field (p : out_param(ℕ)) [fact(nat.prime p)] (K : Type*) [field K] 
  extends algebra 𝔽_[p]⟮⟮X⟯⟯ K :=
[to_finite_dimensional : finite_dimensional 𝔽_[p]⟮⟮X⟯⟯ K]

attribute [priority 100, instance] eq_char_local_field.to_finite_dimensional

namespace eq_char_local_field

variables (p) (K L : Type*) [field K] [eq_char_local_field p K] [field L] [eq_char_local_field p L]

-- We need to mark this one with high priority to avoid timeouts. (TODO: Check)
--@[priority 100000] instance : is_scalar_tower 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯ K := sorry infer_instance

protected lemma is_algebraic : algebra.is_algebraic 𝔽_[p]⟮⟮X⟯⟯ K := algebra.is_algebraic_of_finite _ _

@[priority 100] instance char_p : char_p K p := 
char_p_of_injective_algebra_map (algebra_map 𝔽_[p]⟮⟮X⟯⟯ K).injective p

/-- The ring of integers of an equal characteristic local field is the integral closure of 𝔽_[p]⟦X⟧
  in the local field. -/
def ring_of_integers := integral_closure 𝔽_[p]⟦X⟧ K

localized "notation (name := ring_of_integers)
  `𝓞` := eq_char_local_field.ring_of_integers" in eq_char_local_field

lemma mem_ring_of_integers (x : K) : x ∈ 𝓞 p K ↔ is_integral 𝔽_[p]⟦X⟧ x := iff.rfl

-- TODO: Same proof as in mixed char case
lemma is_integral_of_mem_ring_of_integers {x : K} (hx : x ∈ 𝓞 p K) :
  is_integral 𝔽_[p]⟦X⟧ (⟨x, hx⟩ : 𝓞 p K) :=
begin
  obtain ⟨P, hPm, hP⟩ := hx,
  refine ⟨P, hPm, _⟩,
  rw [← polynomial.aeval_def, ← subalgebra.coe_eq_zero, polynomial.aeval_subalgebra_coe,
    polynomial.aeval_def,  subtype.coe_mk, hP],
end

-- TODO: Same proof as in mixed char case
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

-- Making FpX_int_completion.is_fraction_ring explicit speeds out the proof
instance : is_fraction_ring (𝓞 p K) K := 
@integral_closure.is_fraction_ring_of_finite_extension 
  𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯ _ _ K _ _ _ FpX_int_completion.is_fraction_ring _ _ _ _

instance : is_integral_closure (𝓞 p K) 𝔽_[p]⟦X⟧ K := integral_closure.is_integral_closure _ _

-- Making FpX_int_completion.is_fraction_ring explicit speeds out the proof

instance is_integrally_closed : is_integrally_closed (𝓞 p K) :=
@integral_closure.is_integrally_closed_of_finite_extension _ _ 𝔽_[p]⟮⟮X⟯⟯ _ _ _
  FpX_int_completion.is_fraction_ring _ _ _ _ _ _

-- These two instances speed up the proof of `equiv` a bit.
instance : algebra 𝔽_[p]⟦X⟧ (𝓞 p K) := infer_instance

instance : is_scalar_tower 𝔽_[p]⟦X⟧ (𝓞 p K) K := infer_instance

lemma is_integral_coe (x : 𝓞 p K) : is_integral 𝔽_[p]⟦X⟧ (x : K) := x.2

/-- The ring of integers of `K` is equivalent to any integral closure of `𝔽_[p]⟦X⟧` in `K` -/
protected def equiv (R : Type*) [comm_ring R] [algebra 𝔽_[p]⟦X⟧ R] [algebra R K]
  [is_scalar_tower 𝔽_[p]⟦X⟧ R K] [is_integral_closure R 𝔽_[p]⟦X⟧ K] : 𝓞 p K ≃+* R :=
(is_integral_closure.equiv 𝔽_[p]⟦X⟧ R K (𝓞 p K)).symm.to_ring_equiv

variables (K)

instance : char_p (𝓞 p K) p := char_p.subring' K p (𝓞 p K).to_subring

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

end ring_of_integers

end eq_char_local_field

namespace FpX_field_completion

open eq_char_local_field

-- TODO: change comment
instance eq_char_local_field (p : ℕ) [fact(nat.prime p)] : 
  eq_char_local_field p 𝔽_[p]⟮⟮X⟯⟯ :=
{ to_finite_dimensional :=
  -- The vector space structure of `ℚ` over itself can arise in multiple ways:
  -- all fields are vector spaces over themselves (used in `rat.finite_dimensional`)
  -- all char 0 fields have a canonical embedding of `ℚ` (used in `mixed_char_local_field`).
  -- Show that these coincide:
  by convert (infer_instance : finite_dimensional 𝔽_[p]⟮⟮X⟯⟯ 𝔽_[p]⟮⟮X⟯⟯), }

-- NOTE: Helping out the type class inference system speeds out the proof a lot.
/-- The ring of integers of `𝔽_[p]⟮⟮X⟯⟯` as a mixed characteristic local field is just `𝔽_[p]⟦X⟧`. -/
def ring_of_integers_equiv (p : ℕ) [fact(nat.prime p)] :
  ring_of_integers p 𝔽_[p]⟮⟮X⟯⟯ ≃+* 𝔽_[p]⟦X⟧ := 
--by apply ring_of_integers.equiv --10.4s
begin  --1.3s
  have h := @ring_of_integers.equiv p _ 𝔽_[p]⟮⟮X⟯⟯ _ _ 𝔽_[p]⟦X⟧ _ _ (FpX_int_completion p).algebra
    (is_scalar_tower.left 𝔽_[p]⟦X⟧), 
  have h1 := FpX_int_completion.FpX_field_completion.is_integral_closure p,
  exact @h h1,
end

end FpX_field_completion