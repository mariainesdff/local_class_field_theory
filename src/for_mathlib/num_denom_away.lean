/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import ring_theory.localization.away
import ring_theory.localization.fraction_ring
import ring_theory.localization.integer
import ring_theory.unique_factorization_domain

/-!
# Numerator and denominator in a localization

## Implementation notes

See `src/ring_theory/localization/basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/
variables {R : Type*} [comm_ring R] (M : submonoid R) {S : Type*} [comm_ring S]
variables [algebra R S] {P : Type*} [comm_ring P]

namespace is_fraction_ring

open is_localization

section num_denom

variables (A : Type*) [comm_ring A] [is_domain A] [unique_factorization_monoid A]
variables {K : Type*} [field K] [algebra A K] [is_fraction_ring A K]

lemma exists_reduced_fraction (x : K) :
  ∃ (a : A) (b : non_zero_divisors A),
  (∀ {d}, d ∣ a → d ∣ b → is_unit d) ∧ mk' K a b = x :=
begin
  obtain ⟨⟨b, b_nonzero⟩, a, hab⟩ := exists_integer_multiple (non_zero_divisors A) x,
  obtain ⟨a', b', c', no_factor, rfl, rfl⟩ :=
    unique_factorization_monoid.exists_reduced_factors' a b
      (mem_non_zero_divisors_iff_ne_zero.mp b_nonzero),
  obtain ⟨c'_nonzero, b'_nonzero⟩ := mul_mem_non_zero_divisors.mp b_nonzero,
  refine ⟨a', ⟨b', b'_nonzero⟩, @no_factor, _⟩,
  refine mul_left_cancel₀
    (is_fraction_ring.to_map_ne_zero_of_mem_non_zero_divisors b_nonzero) _,
  simp only [subtype.coe_mk, ring_hom.map_mul, algebra.smul_def] at *,
  erw [←hab, mul_assoc, mk'_spec' _ a' ⟨b', b'_nonzero⟩],
end

/-- `f.num x` is the numerator of `x : f.codomain` as a reduced fraction. -/
noncomputable def num (x : K) : A :=
classical.some (exists_reduced_fraction A x)

/-- `f.num x` is the denominator of `x : f.codomain` as a reduced fraction. -/
noncomputable def denom (x : K) : non_zero_divisors A :=
classical.some (classical.some_spec (exists_reduced_fraction A x))

lemma num_denom_reduced (x : K) {d} : d ∣ num A x → d ∣ denom A x → is_unit d :=
(classical.some_spec (classical.some_spec (exists_reduced_fraction A x))).1

@[simp] lemma mk'_num_denom (x : K) : mk' K (num A x) (denom A x) = x :=
(classical.some_spec (classical.some_spec (exists_reduced_fraction A x))).2

variables {A}

lemma num_mul_denom_eq_num_iff_eq {x y : K} :
  x * algebra_map A K (denom A y) = algebra_map A K (num A y) ↔ x = y :=
⟨λ h, by simpa only [mk'_num_denom] using eq_mk'_iff_mul_eq.mpr h,
 λ h, eq_mk'_iff_mul_eq.mp (by rw [h, mk'_num_denom])⟩

lemma num_mul_denom_eq_num_iff_eq' {x y : K} :
  y * algebra_map A K (denom A x) = algebra_map A K (num A x) ↔ x = y :=
⟨λ h, by simpa only [eq_comm, mk'_num_denom] using eq_mk'_iff_mul_eq.mpr h,
 λ h, eq_mk'_iff_mul_eq.mp (by rw [h, mk'_num_denom])⟩

lemma num_mul_denom_eq_num_mul_denom_iff_eq {x y : K} :
  num A y * denom A x = num A x * denom A y ↔ x = y :=
⟨λ h, by simpa only [mk'_num_denom] using mk'_eq_of_eq h,
 λ h, by rw h⟩

lemma eq_zero_of_num_eq_zero {x : K} (h : num A x = 0) : x = 0 :=
num_mul_denom_eq_num_iff_eq'.mp (by rw [zero_mul, h, ring_hom.map_zero])

lemma is_integer_of_is_unit_denom {x : K} (h : is_unit (denom A x : A)) : is_integer A x :=
begin
  cases h with d hd,
  have d_ne_zero : algebra_map A K (denom A x) ≠ 0 :=
    is_fraction_ring.to_map_ne_zero_of_mem_non_zero_divisors (denom A x).2,
  use ↑d⁻¹ * num A x,
  refine trans _ (mk'_num_denom A x),
  rw [map_mul, map_units_inv, hd],
  apply mul_left_cancel₀ d_ne_zero,
  rw [←mul_assoc, mul_inv_cancel d_ne_zero, one_mul, mk'_spec']
end

lemma is_unit_denom_of_num_eq_zero {x : K} (h : num A x = 0) : is_unit (denom A x : A) :=
num_denom_reduced A x (h.symm ▸ dvd_zero _) dvd_rfl

end num_denom

variables (S)
universes u v

section away

variables {A : Type u} [decidable_eq A]
variables [cancel_comm_monoid_with_zero A] [normalization_monoid A] [unique_factorization_monoid A]
variables [dec_dvd : decidable_rel (has_dvd.dvd : A → A → Prop)]
variable {x : A}
variable (hx : irreducible x)
open multiplicity unique_factorization_monoid

end away

section away

open multiplicity unique_factorization_monoid

variables {A : Type u} [comm_ring A] [is_domain A]
variables [dec_dvd : decidable_rel (has_dvd.dvd : A → A → Prop)]
variable (x : A)
variables (B : Type v) [comm_ring B] [algebra A B] [is_localization.away x B] 
variable (hx' : irreducible x)
variable (n : ℕ)

#where

include dec_dvd

lemma uno_remarkable (a₀ : A) (h : a₀ ≠ 0) [nontrivial A] (hx : irreducible x) : 
  ∃ n : ℕ, ∃ a : A, ¬ x ∣ a ∧ a₀ = x ^ n * a :=
begin
  let n := (normalized_factors a₀).count (normalize x),
  obtain ⟨a, ha1, ha2⟩ := (@exists_eq_pow_mul_and_not_dvd A _ _ x a₀
    (ne_top_iff_finite.mp (part_enat.ne_top_iff.mpr _))),
  simp_rw [← (multiplicity_eq_count_normalized_factors hx h).symm] at ha1,
  use [n, a, ha2, ha1],
  use [n, (multiplicity_eq_count_normalized_factors hx h)],
end

lemma due_remarkable (a : A) (m n : ℕ) :
  (mk' B a ⟨x^n, (submonoid.mem_powers_iff (x^n) x).mpr ⟨n, rfl⟩⟩) = 
  (mk' B (a * x^m) ⟨x^(n), (submonoid.mem_powers_iff (x^n) x).mpr ⟨n, rfl⟩⟩) :=
begin
sorry
end

-- include x

-- noncomputable def inv_self.unit : Bˣ :=
--   ⟨away.inv_self x, algebra_map _ _ x, by {rw mul_comm, exact away.mul_inv_self _},
--     away.mul_inv_self _⟩

noncomputable def x_as_unit : Bˣ :=
  ⟨algebra_map _ _ x, away.inv_self x, away.mul_inv_self _,
    by {rw mul_comm, exact away.mul_inv_self _}⟩


lemma due_remarkable' (a : A) (b : B) (m d : ℤ) :
  (((x_as_unit x B ^ (m - d)) : Bˣ ) : B) * mk' B a (1 : submonoid.powers x) = b ↔
  (((x_as_unit x B ^ m) : Bˣ) : B) * mk' B a (1 : submonoid.powers x) = (((x_as_unit x B ^ d) : Bˣ) : B) * b :=
begin
sorry
end

lemma aux (d : ℕ) : (((x_as_unit x B)^(d : ℤ) : Bˣ) : B) = (algebra_map A B x)^d := sorry --rfl
#check aux x B

include hx'

-- the following `lemma` is false: it can happen that `b` is integral. 
lemma exists_reduced_fraction' (b : B) (hb : b ≠ 0) :
  ∃ (a : A) (n : ℤ), ¬ x ∣ a ∧
  (((x_as_unit x B)^n : Bˣ) : B) * mk' B a (1 : submonoid.powers x) = b :=
  -- (mk' B a (1 : (submonoid.powers x))) * (((away.inv_self x) : Bˣ ) : B)= b :=
  -- (∀ {d}, d ∣ a → d ∣ b → is_unit d) ∧ mk' K a b = x :=
begin
  obtain ⟨⟨a₀, y⟩, H⟩ := is_localization.surj (submonoid.powers x) b,
  obtain ⟨d, hy⟩ := (submonoid.mem_powers_iff y.1 x).mp y.2,
    have ha₀ : a₀ ≠ 0,
    { --have : (y : A) ≠ 0,
      -- rw coe_zero,
      -- by_contra,
      have h_inj := @is_localization.injective A _ (submonoid.powers x) B _ _ _ 
        (powers_le_non_zero_divisors_of_no_zero_divisors (hx'.ne_zero)),
      haveI := @is_domain_of_le_non_zero_divisors B _ A _ _ _ (submonoid.powers x) _
       (powers_le_non_zero_divisors_of_no_zero_divisors hx'.ne_zero),
      simp only [map_zero, ← subtype.val_eq_coe, ← hy, map_pow] at H,
      apply ((injective_iff_map_eq_zero' (algebra_map A B)).mp (h_inj) a₀).mpr.mt,
      rw ← H,
      apply mul_ne_zero hb,
      apply pow_ne_zero,
      apply @is_localization.to_map_ne_zero_of_mem_non_zero_divisors
        A _ (submonoid.powers x) B _ _ _ _ _ x _,
      apply powers_le_non_zero_divisors_of_no_zero_divisors (hx'.ne_zero),
      exact mem_non_zero_divisors_iff_ne_zero.mpr hx'.ne_zero,
    },
    simp only [← subtype.val_eq_coe, ← hy] at H,--needed?
    obtain ⟨m, a, hyp1, hyp2⟩ := uno_remarkable x a₀ ha₀ hx',
    use a,
    use m - d,
    rw [due_remarkable' x B a b m d, aux x B d, mul_comm _ b, ← map_pow, H, hyp2, aux x B m,
      map_mul, map_pow],
    exact ⟨hyp1, (congr_arg _ (is_localization.mk'_one _ _))⟩,
end

end away

end is_fraction_ring
