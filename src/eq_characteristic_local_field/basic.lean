/-
Copyright (c) 2022 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import field_theory.finite.galois_field
import ring_theory.dedekind_domain.adic_valuation
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
open polynomial multiplicative ratfunc

variables (p : ℕ) [fact(nat.prime p)] 

notation (name := prime_galois_field)
  `𝔽_[` p `]` := galois_field p 1

noncomputable! def ideal_X :
  is_dedekind_domain.height_one_spectrum (polynomial 𝔽_[p]) :=
{ as_ideal := ideal.span({X}),
  is_prime := by { rw ideal.span_singleton_prime, exacts [prime_X, X_ne_zero] },
  ne_bot   := by { rw [ne.def, ideal.span_singleton_eq_bot], exact X_ne_zero }} 

/- The valued field `Fp(X)` with the valuation at `X`. -/
noncomputable! def FpX_valued  : valued (ratfunc 𝔽_[p]) ℤₘ₀ :=
valued.mk' (ideal_X p).valuation

lemma FqX_valued_def {x : ratfunc 𝔽_[p]} :
  @valued.v (ratfunc 𝔽_[p]) _ _ _ (FpX_valued p) x = (ideal_X p).valuation x := rfl 

def FpX_field_completion  :=
 (ideal_X p).adic_completion (ratfunc 𝔽_[p])

notation (name := FpX_field_completion)
  `𝔽_[` p `]⟮⟮` X `⟯⟯` := FpX_field_completion p

def FpX_int_completion  :=
 (ideal_X p).adic_completion_integers (ratfunc 𝔽_[p])

notation (name := FpX_int_completion)
  `𝔽_[` p `]⟦` X `⟧` := FpX_int_completion p

variable {p}

instance : field 𝔽_[p]⟮⟮X⟯⟯ :=  --sorry
is_dedekind_domain.height_one_spectrum.adic_completion.field (ratfunc 𝔽_[p]) (ideal_X p)

instance : inhabited (FpX_field_completion p) := ⟨(0 : FpX_field_completion p)⟩

-- Upgrade to (ratfunc Fp)-algebra iso
noncomputable! def isom_laurent : 𝔽_[p]⟮⟮X⟯⟯  ≃+* (laurent_series 𝔽_[p]) := sorry -- F

-- Upgrade to (ratfunc Fp)-algebra iso
noncomputable! def isom_power_series : 𝔽_[p]⟦X⟧  ≃+* (power_series 𝔽_[p]) := sorry -- F

instance : algebra 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯ :=
(by apply_instance : algebra ((ideal_X p).adic_completion_integers (ratfunc 𝔽_[p]))
  ((ideal_X p).adic_completion (ratfunc 𝔽_[p])))

noncomputable! instance : is_fraction_ring 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯ := --sorry  -- F
(by apply_instance : is_fraction_ring ((ideal_X p).adic_completion_integers (ratfunc 𝔽_[p]))
  ((ideal_X p).adic_completion (ratfunc 𝔽_[p])))

-- For instances and lemmas that only need `K` to be an `𝔽_[p]⟮⟮X⟯⟯`-algebra
namespace adic_algebra

variables (K L : Type*) [field K] [algebra 𝔽_[p]⟮⟮X⟯⟯ K] [field L]
  [algebra 𝔽_[p]⟮⟮X⟯⟯ L]

-- Q: Is there a general algebra.comp? I think we could prove all of these instances in that generality
instance to_int_algebra : algebra 𝔽_[p]⟦X⟧ K := 
(ring_hom.comp (algebra_map 𝔽_[p]⟮⟮X⟯⟯ K) (algebra_map 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯)).to_algebra

@[simp] lemma int_algebra_map_def : algebra_map 𝔽_[p]⟦X⟧ K = 
  (adic_algebra.to_int_algebra K).to_ring_hom := rfl 

@[priority 10000] instance : is_scalar_tower 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯ K :=
⟨λ _ _ _, by simp only [algebra.smul_def, int_algebra_map_def, map_mul, ← mul_assoc]; refl⟩

@[priority 1000] instance int_is_scalar_tower [algebra K L] [is_scalar_tower 𝔽_[p]⟮⟮X⟯⟯ K L] :
  is_scalar_tower 𝔽_[p]⟦X⟧ K L :=
{ smul_assoc := λ x y z,
  begin
    nth_rewrite 0 [← one_smul 𝔽_[p]⟮⟮X⟯⟯ y],
    rw [← one_smul 𝔽_[p]⟮⟮X⟯⟯ (y • z), ← smul_assoc, ← smul_assoc, ← smul_assoc],
  end }

lemma algebra_map_injective {E : Type*} [field E] [algebra 𝔽_[p]⟦X⟧ E] [algebra 𝔽_[p]⟮⟮X⟯⟯ E]
  [is_scalar_tower 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯ E] : function.injective ⇑(algebra_map 𝔽_[p]⟦X⟧ E) :=
begin
  rw is_scalar_tower.algebra_map_eq 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯ E,
  exact function.injective.comp ((algebra_map 𝔽_[p]⟮⟮X⟯⟯ E).injective)
    (is_fraction_ring.injective 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯)
end

end adic_algebra

variables (K L : Type*) [field K] [hK : algebra 𝔽_[p]⟮⟮X⟯⟯ K] [field L]
  [algebra 𝔽_[p]⟮⟮X⟯⟯ L]

/-- An equal characteristic local field is a field which is finite
dimensional over `𝔽_p((X))`, for some prime `p`. -/
class eq_char_local_field (K : Type*) [field K] extends algebra 𝔽_[p]⟮⟮X⟯⟯ K :=
[to_finite_dimensional : finite_dimensional 𝔽_[p]⟮⟮X⟯⟯ K]



/- 


noncomputable theory

/-- A mixed characteristic local field is a field which has characteristic zero and is finite
dimensional over `ℚ_[p]`, for some prime `p`. -/
class mixed_char_local_field (p : out_param(ℕ)) [fact(nat.prime p)] (K : Type*) [field K]
  extends algebra ℚ_[p] K :=
[to_char_zero : char_zero K]
[to_finite_dimensional : finite_dimensional ℚ_[p] K] 

attribute [nolint dangerous_instance] mixed_char_local_field.to_char_zero

-- See note [lower instance priority]
attribute [priority 100, instance] mixed_char_local_field.to_char_zero
  mixed_char_local_field.to_finite_dimensional

namespace mixed_char_local_field

variables (p : ℕ) [fact(nat.prime p)] (K L : Type*) [field K] [mixed_char_local_field p K] [field L]
  [mixed_char_local_field p L]

-- We need to mark this one with high priority to avoid timeouts.
@[priority 10000] instance : is_scalar_tower ℤ_[p] ℚ_[p] K := infer_instance

protected lemma is_algebraic : algebra.is_algebraic ℚ_[p] K := algebra.is_algebraic_of_finite _ _

/-- The ring of integers of a mixed characteristic local field is the integral closure of ℤ_[p]
  in the local field. -/
def ring_of_integers := integral_closure ℤ_[p] K

localized "notation (name := ring_of_integers)
  `𝓞` := mixed_char_local_field.ring_of_integers" in mixed_char_local_field

lemma mem_ring_of_integers (x : K) : x ∈ 𝓞 p K ↔ is_integral ℤ_[p] x := iff.rfl

lemma is_integral_of_mem_ring_of_integers {x : K} (hx : x ∈ 𝓞 p K) :
  is_integral ℤ_[p] (⟨x, hx⟩ : 𝓞 p K) :=
begin
  obtain ⟨P, hPm, hP⟩ := hx,
  refine ⟨P, hPm, _⟩,
  rw [← polynomial.aeval_def, ← subalgebra.coe_eq_zero, polynomial.aeval_subalgebra_coe,
    polynomial.aeval_def,  subtype.coe_mk, hP],
end

/-- Given an algebra between two local fields over ℚ_[p], create an algebra between their two rings
of integers. For now, this is not an instance by default as it creates an equal-but-not-defeq
diamond with `algebra.id` when `K = L`. This is caused by `x = ⟨x, x.prop⟩` not being defeq on
subtypes. This will likely change in Lean 4. -/
def ring_of_integers_algebra [algebra K L] [is_scalar_tower ℚ_[p] K L] : algebra (𝓞 p K) (𝓞 p L) := 
ring_hom.to_algebra
{ to_fun := λ k, ⟨algebra_map K L k, is_integral.algebra_map k.2⟩,
  map_zero' := subtype.ext $ by simp only [subtype.coe_mk, subalgebra.coe_zero, map_zero],
  map_one'  := subtype.ext $ by simp only [subtype.coe_mk, subalgebra.coe_one, map_one],
  map_add'  := λ x y, subtype.ext $ by simp only [map_add, subalgebra.coe_add, subtype.coe_mk],
  map_mul'  := λ x y, subtype.ext $ by simp only [subalgebra.coe_mul, map_mul, subtype.coe_mk] }

namespace ring_of_integers

variables {K}

--set_option trace.class_instances true
-- I had to increase the priority of `mixed_char_local_field.is_scalar_tower` for this to work.
-- Otherwise it times out if the is_scalar_tower argument is implicit
noncomputable! instance : is_fraction_ring (𝓞 p K) K := 
integral_closure.is_fraction_ring_of_finite_extension ℚ_[p] _

instance : is_integral_closure (𝓞 p K) ℤ_[p] K :=
integral_closure.is_integral_closure _ _

-- Times out if the is_scalar_tower argument is implicit (without the priority fix)
noncomputable! instance : is_integrally_closed (𝓞 p K) :=
integral_closure.is_integrally_closed_of_finite_extension ℚ_[p]

lemma is_integral_coe (x : 𝓞 p K) : is_integral ℤ_[p] (x : K) := x.2

/-- The ring of integers of `K` is equivalent to any integral closure of `ℤ_[p]` in `K` -/
protected noncomputable! def equiv (R : Type*) [comm_ring R] [algebra ℤ_[p] R] [algebra R K]
  [is_scalar_tower ℤ_[p] R K] [is_integral_closure R ℤ_[p] K] : 𝓞 p K ≃+* R :=
(is_integral_closure.equiv ℤ_[p] R K _).symm.to_ring_equiv

variables (K)

instance : char_zero (𝓞 p K) := char_zero.of_module _ K

noncomputable! instance : is_noetherian ℤ_[p] (𝓞 p K) :=
is_integral_closure.is_noetherian _ ℚ_[p] K _

noncomputable! lemma algebra_map_injective :
  function.injective ⇑(algebra_map ℤ_[p] (ring_of_integers p K)) := 
begin
  have hinj : function.injective ⇑(algebra_map ℤ_[p] K),
  { rw is_scalar_tower.algebra_map_eq ℤ_[p] ℚ_[p] K,
    exact function.injective.comp ((algebra_map ℚ_[p] K).injective)
      (is_fraction_ring.injective ℤ_[p] ℚ_[p]), },
  rw injective_iff_map_eq_zero (algebra_map ℤ_[p] ↥(𝓞 p K)),
  intros x hx,
  rw [← subtype.coe_inj, subalgebra.coe_zero] at hx,
  rw injective_iff_map_eq_zero (algebra_map ℤ_[p] K) at hinj,
  exact hinj x hx,
end

/-- The ring of integers of a mixed characteristic local field is not a field. -/
lemma not_is_field : ¬ is_field (𝓞 p K) :=
by simpa [← (is_integral_closure.is_integral_algebra ℤ_[p] K).is_field_iff_is_field
  (algebra_map_injective p K)] using (padic_int.not_is_field p)

noncomputable! instance : is_dedekind_domain (𝓞 p K) :=
is_integral_closure.is_dedekind_domain ℤ_[p] ℚ_[p] K _

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

end mixed_char_local_field

namespace padic

open mixed_char_local_field

instance mixed_char_local_field (p : ℕ) [fact(nat.prime p)] : mixed_char_local_field p ℚ_[p] :=
{ to_char_zero := infer_instance,
  to_finite_dimensional :=
    -- The vector space structure of `ℚ` over itself can arise in multiple ways:
    -- all fields are vector spaces over themselves (used in `rat.finite_dimensional`)
    -- all char 0 fields have a canonical embedding of `ℚ` (used in `mixed_char_local_field`).
    -- Show that these coincide:
    by convert (infer_instance : finite_dimensional ℚ_[p] ℚ_[p]), }

/-- The ring of integers of `ℚ_[p]` as a mixed characteristic local field is just `ℤ_[p]`. -/
noncomputable def ring_of_integers_equiv (p : ℕ) [fact(nat.prime p)] :
  ring_of_integers p ℚ_[p] ≃+* ℤ_[p] :=
ring_of_integers.equiv p ℤ_[p]

end padic-/