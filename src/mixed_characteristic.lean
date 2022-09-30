/-
Copyright (c) 2022 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import ring_theory.dedekind_domain.integral_closure
import algebra.char_p.algebra
import number_theory.padics.padic_integers


/-!
# Mixed characteristic local fields fields
This file defines a number field, the ring of integers corresponding to it and includes some
basic facts about the embeddings into an algebraic closed field.
## Main definitions
 - `mixed_char_local_field` defines a number field as a field which has characteristic zero and is finite
    dimensional over ℚ.
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
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1970algebraic]
## Tags
number field, ring of integers
-/

noncomputable theory

/-- A mixed characteristic local field is a field which has characteristic zero and is finite
dimensional over `ℚ_[p]`, for some prime `p`. -/
class mixed_char_local_field (p : ℕ) [fact(nat.prime p)] (K : Type*) [field K] [algebra ℚ_[p] K] :=
[to_char_zero : char_zero K]
[to_finite_dimensional : finite_dimensional ℚ_[p] K]

class mixed_char_local_field' (p : ℕ) [fact(nat.prime p)] (K : Type*) [field K]
extends algebra ℚ_[p] K :=
[to_char_zero : char_zero K]
[to_finite_dimensional : finite_dimensional ℚ_[p] K]

/- class mixed_char_local_field (p : ℕ) [fact(nat.prime p)] (K : Type*) [field K] [module ℚ_[p] K] :=
[to_char_zero : char_zero K]
[to_finite_dimensional : finite_dimensional ℚ_[p] K] -/

open function
open_locale classical big_operators

/-- `ℤ_[p]` with its usual ring structure is not a field. -/
lemma padic_int.not_is_field (p : ℕ) [hp : fact(nat.prime p)] : ¬ is_field ℤ_[p] :=
begin
  rw ring.not_is_field_iff_exists_ideal_bot_lt_and_lt_top,
  use ideal.span {(p : ℤ_[p])},
  split,
  { rw [bot_lt_iff_ne_bot, ne.def, ideal.span_singleton_eq_bot, nat.cast_eq_zero],
    exact hp.1.ne_zero },
  { rw [lt_top_iff_ne_top, ne.def, ideal.eq_top_iff_one, ideal.mem_span_singleton,
      ← padic_int.norm_lt_one_iff_dvd, norm_one, not_lt], }
end

namespace mixed_char_local_field

variables (p : ℕ) [fact(nat.prime p)] (K L : Type*) [field K] [hK : algebra ℚ_[p] K]/-[module ℚ_[p] K]-/
  [field L] [algebra ℚ_[p] L] [mixed_char_local_field p K] [mixed_char_local_field p L]

variables (E : Type*) [field E] [mixed_char_local_field' p E]

-- See note [lower instance priority]
attribute [priority 100, instance] mixed_char_local_field.to_char_zero
  mixed_char_local_field.to_finite_dimensional

--instance : algebra ℚ_[p] K := sorry

instance padic.algebra : algebra ℤ_[p] ℚ_[p] := ring_hom.to_algebra (padic_int.coe.ring_hom) --It seems this is missing?

@[simp] lemma padic.algebra_map_def : algebra_map ℤ_[p] ℚ_[p] =  padic_int.coe.ring_hom := rfl
--instance padic.is_scalar_tower : is_scalar_tower ℤ_[p] ℤ_[p] ℚ_[p] := 
instance padic.is_fraction_ring : is_fraction_ring ℤ_[p] ℚ_[p] := sorry -- And this
instance padic_is_integral_closure : is_integral_closure ℤ_[p] ℤ_[p] ℚ_[p] := begin
  sorry
end

instance : algebra ℤ_[p] E := (ring_hom.comp
  (@mixed_char_local_field'.to_algebra p _ E _ _).to_ring_hom
  (@padic_int.coe.ring_hom p _)).to_algebra

include hK

instance mixed_char_local_field.to_algebra : algebra ℤ_[p] K :=
(ring_hom.comp hK.to_ring_hom (@padic_int.coe.ring_hom p _)).to_algebra

@[simp] lemma algebra_map_def : algebra_map ℤ_[p] K = 
  ring_hom.comp hK.to_ring_hom (@padic_int.coe.ring_hom p _) := rfl

instance : is_scalar_tower ℤ_[p] ℚ_[p] K :=
⟨λ _ _ _, begin
  simp only [algebra.smul_def, algebra_map_def, padic.algebra_map_def, map_mul,
    ring_hom.comp_apply, ← mul_assoc],
  refl,
end⟩

instance mixed_char_local_field'.scalar_tower : is_scalar_tower ℤ_[p] ℚ_[p] E :=
⟨λ _ _ _, begin
  simp only [algebra.smul_def, algebra_map_def, padic.algebra_map_def, map_mul,
    ring_hom.comp_apply, ← mul_assoc],
  refl,
end⟩

-- Does not work if mixed_char_local_field only assumes `module ℚ_[p] K`. Diamond?
protected lemma is_algebraic : algebra.is_algebraic ℚ_[p] K := algebra.is_algebraic_of_finite _ _

lemma algebra_map_injective [algebra ℤ_[p] K] [algebra ℚ_[p] K]
  [is_scalar_tower ℤ_[p] ℚ_[p] K] : function.injective ⇑(algebra_map ℤ_[p] K) :=
begin
  rw is_scalar_tower.algebra_map_eq ℤ_[p] ℚ_[p] K,
  exact function.injective.comp ((algebra_map ℚ_[p] K).injective)
    (is_fraction_ring.injective ℤ_[p] ℚ_[p])
end


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

instance asdf [algebra K L] [is_scalar_tower ℚ_[p] K L] : is_scalar_tower ℤ_[p] K L :=
sorry

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

instance : is_fraction_ring (𝓞 p K) K :=
integral_closure.is_fraction_ring_of_finite_extension ℚ_[p] _

instance : is_integral_closure (𝓞 p K) ℤ_[p] K :=
integral_closure.is_integral_closure _ _

instance : is_integrally_closed (𝓞 p K) :=
integral_closure.is_integrally_closed_of_finite_extension ℚ_[p]

lemma is_integral_coe (x : 𝓞 p K) : is_integral ℤ_[p] (x : K) :=
x.2


/-- The ring of integers of `K` is equivalent to any integral closure of `ℤ_[p]` in `K` -/
protected noncomputable def equiv (R : Type*) [comm_ring R] [algebra ℤ_[p] R] [algebra R K]
  [is_scalar_tower ℤ_[p] R K] [is_integral_closure R ℤ_[p] K] : 𝓞 p K ≃+* R :=
(is_integral_closure.equiv ℤ_[p] R K _).symm.to_ring_equiv

variables (K)

instance : char_zero (𝓞 p K) := char_zero.of_module _ K

instance : is_noetherian ℤ (𝓞 p K) := sorry -- is_integral_closure.is_noetherian _ ℚ K _

lemma algebra_map_injective :
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

instance : is_dedekind_domain (𝓞 p K) :=
is_integral_closure.is_dedekind_domain ℤ_[p] ℚ_[p] K _

-- TODO : ring of integers is local

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

end padic


section valuation
/- 
* Topology on K + this is locally compact.
* Define normalized discrete valuation on K, using topological nilpotent elements.
* Unit ball = ring of integers
* Top. nilp. elements are a maximal ideal P in O_K
* Define ramification index e
* P^e = (p)
* Relate to norm (future)
-/
end valuation


#exit

namespace adjoin_root

section

open_locale polynomial

local attribute [-instance] algebra_rat

/-- The quotient of `ℚ_[p][X]` by the ideal generated by an irreducible polynomial of `ℚ_[p][X]`
is a mixed characterstic local field. -/
noncomputable! instance  (p : ℕ) [fact(nat.prime p)] {f : ℚ_[p][X]} [hf : fact (irreducible f)] :
  mixed_char_local_field p (adjoin_root f) :=
{ to_char_zero := sorry, --char_zero_of_injective_algebra_map (algebra_map ℚ _).injective,
  to_finite_dimensional := sorry, } 
  --by convert (adjoin_root.power_basis hf.out.ne_zero).finite_dimensional }
end



end adjoin_root

namespace mixed_char_local_field.embeddings

section fintype

open finite_dimensional

variables (K : Type*) [field K] [mixed_char_local_field K]
variables (A : Type*) [field A] [char_zero A]

/-- There are finitely many embeddings of a number field. -/
noncomputable instance : fintype (K →+* A) := fintype.of_equiv (K →ₐ[ℚ] A)
ring_hom.equiv_rat_alg_hom.symm

variables [is_alg_closed A]

/-- The number of embeddings of a number field is equal to its finrank. -/
lemma card : fintype.card (K →+* A) = finrank ℚ K :=
by rw [fintype.of_equiv_card ring_hom.equiv_rat_alg_hom.symm, alg_hom.card]

end fintype

section roots

open set polynomial

/-- Let `A` an algebraically closed field and let `x ∈ K`, with `K` a number field. For `F`,
subfield of `K`, the images of `x` by the `F`-algebra morphisms from `K` to `A` are exactly
the roots in `A` of the minimal polynomial of `x` over `F` -/
lemma range_eq_roots (F K A : Type*) [field F] [mixed_char_local_field F] [field K] [mixed_char_local_field K]
  [field A] [is_alg_closed A] [algebra F K] [algebra F A] (x : K) :
  range (λ ψ : K →ₐ[F] A, ψ x) = (minpoly F x).root_set A :=
begin
  haveI : finite_dimensional F K := finite_dimensional.right ℚ  _ _ ,
  have hx : is_integral F x := is_separable.is_integral F x,
  ext a, split,
  { rintro ⟨ψ, hψ⟩,
    rw [mem_root_set_iff, ←hψ],
    { rw aeval_alg_hom_apply ψ x (minpoly F x),
      simp only [minpoly.aeval, map_zero], },
    exact minpoly.ne_zero hx, },
  { intro ha,
    let Fx := adjoin_root (minpoly F x),
    haveI : fact (irreducible $ minpoly F x) := ⟨minpoly.irreducible hx⟩,
    have hK : (aeval x) (minpoly F x) = 0 := minpoly.aeval _ _,
    have hA : (aeval a) (minpoly F x) = 0,
    { rwa [aeval_def, ←eval_map, ←mem_root_set_iff'],
      exact monic.ne_zero (monic.map (algebra_map F A) (minpoly.monic hx)), },
    letI : algebra Fx A := ring_hom.to_algebra (by convert adjoin_root.lift (algebra_map F A) a hA),
    letI : algebra Fx K := ring_hom.to_algebra (by convert adjoin_root.lift (algebra_map F K) x hK),
    haveI : finite_dimensional Fx K := finite_dimensional.right ℚ  _ _ ,
    let ψ₀ : K →ₐ[Fx] A := is_alg_closed.lift (algebra.is_algebraic_of_finite _ _),
    haveI : is_scalar_tower F Fx K := is_scalar_tower.of_ring_hom (adjoin_root.lift_hom _ _ hK),
    haveI : is_scalar_tower F Fx A := is_scalar_tower.of_ring_hom (adjoin_root.lift_hom _ _ hA),
    let ψ : K →ₐ[F] A := alg_hom.restrict_scalars F ψ₀,
    refine ⟨ψ, _⟩,
    rw (_ : x = (algebra_map Fx K) (adjoin_root.root (minpoly F x))),
    rw (_ : a = (algebra_map Fx A) (adjoin_root.root (minpoly F x))),
    exact alg_hom.commutes _ _,
    exact (adjoin_root.lift_root hA).symm,
    exact (adjoin_root.lift_root hK).symm, },
end

variables (K A : Type*) [field K] [mixed_char_local_field K] [field A] [char_zero A] [is_alg_closed A] (x : K)

/-- Let `A` be an algebraically closed field and let `x ∈ K`, with `K` a number field.
The images of `x` by the embeddings of `K` in `A` are exactly the roots in `A` of
the minimal polynomial of `x` over `ℚ` -/
lemma rat_range_eq_roots :
range (λ φ : K →+* A, φ x) = (minpoly ℚ x).root_set A :=
begin
  convert range_eq_roots ℚ K A x using 1,
  ext a,
  exact ⟨λ ⟨φ, hφ⟩, ⟨φ.to_rat_alg_hom, hφ⟩, λ ⟨φ, hφ⟩, ⟨φ.to_ring_hom, hφ⟩⟩,
end

end roots

end mixed_char_local_field.embeddings