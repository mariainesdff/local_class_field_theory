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

section away

variables (A : Type*) [comm_ring A] [is_domain A]
variables (x : A) {B : Type*} [comm_ring B] [algebra A B] [away x B] [decidable_eq A]
variables [cancel_comm_monoid_with_zero A] [normalization_monoid A] [unique_factorization_monoid A]
variables [dec_dvd : decidable_rel (has_dvd.dvd : A → A → Prop)]
open multiplicity

example (a : Aˣ) (b c : A) (d : ℤ) (hb : is_unit b) : ((hb.some^d : Aˣ) : A) * c = 0 :=
begin
  sorry,
end

include dec_dvd

example (n : ℕ) (a : A) : is_unit (mk' B (1 : A) ⟨x, submonoid.mem_powers _⟩) :=
begin
  apply is_unit_of_mul_eq_one _ (algebra_map A B x),
  convert @mk'_spec_mk A _ (submonoid.powers x) B _ _ _ 1 x (submonoid.mem_powers _),
  exact (map_one _).symm,
end

-- example (n : ℕ) (a : A) : is_unit (mk' B (1 : A) ⟨x, submonoid.mem_powers _⟩^n) :=

example (n : ℕ) (a : A) : is_unit (mk' B (1 : A) ⟨x, submonoid.mem_powers _⟩^n) :=
begin
  -- suffices is_unit 
  apply is_unit_of_mul_eq_one _ (mk' B (x^n) (1 : (submonoid.powers x))),
  suggest,
  -- simp only [map_pow],
  -- simp,
  -- convert @mk'_spec_mk A _ (submonoid.powers x) B _ _ _ 1 (x ^ n)
  --   (pow_mem (submonoid.mem_powers _) n),
  -- swap,
  -- simp only [map_pow],
  -- swap,
  -- exact (map_one _).symm,
  -- -- rw [← localization.mk_eq_monoid_of_mk'],
  -- rw mk',
  -- -- rw mk',
  -- have := @localization.mk_pow A _ (submonoid.powers x) n 1 ⟨x, submonoid.mem_powers _⟩,
  have α := _inst_9.map_units ⟨x ^ n, pow_mem (submonoid.mem_powers _) n⟩,
  convert α,
  simp only [set_like.coe_mk, map_pow],
  refine congr_arg2 pow _ rfl,
  rw mk',
  -- suggest,
  -- simp,
  -- rw this,
  -- simp,
  -- simp only [map_pow],
end

def lsa : has_pow ℤ (submonoid.powers (x)) :=
begin
sorry
end

lemma inv_self_unit : is_unit ((away.inv_self x) : B) :=
begin
  apply is_unit_of_mul_eq_one _ (mk' B x (1 : (submonoid.powers x))),
  simp only [away.inv_self, ←mk'_mul, one_mul, mul_one, mk'_self], 
end

lemma inv_self_pow_unit (n : ℕ) : is_unit ((away.inv_self x)^n : B) := (inv_self_unit A x).pow n

example (hx : irreducible x) (b : B) : true :=
begin
  obtain ⟨b, hb⟩ := inv_self_unit A x,
--  let α : Bˣ,-- := ⟨away.inv_self x, inv_self_unit A x⟩,
--  fconstructor,
--  use away.inv_self x,
--  have := (inv_self_unit A x),
end

example (hx : irreducible x) (b : B) : is_unit (mk' B x (1 : submonoid.powers x)) :=
begin
  apply is_unit_of_mul_eq_one _ (mk' B (x^n) (1 : (submonoid.powers x))),
  convert @map_units A _ (submonoid.powers x) B _ _ _ ⟨x, submonoid.mem_powers _⟩,
  simp,
  rw mk',
  have := _inst_9.1,
  have := _inst_9.2,
  have := _inst_9.3,
  -- have := @map_mk',
end

-- the following `lemma` is false: it can happen that `b` is integral. 
lemma exists_reduced_fraction' (hx : irreducible x) (b : B):
  ∃ (a : A) (n : ℤ), ¬ x ∣ a ∧
  (⟨away.inv_self x, map_units ⟨x, submonoid.mem_powers _⟩⟩ : Bˣ ) = 1 :=
  -- (mk' B a (1 : (submonoid.powers x))) * (((away.inv_self x) : Bˣ ) : B)= b :=
  -- (∀ {d}, d ∣ a → d ∣ b → is_unit d) ∧ mk' K a b = x :=
begin
  -- have : is_unit (mk' B x 1),
  -- convert map_units B ⟨x, submonoid.mem_powers _⟩,
  
  obtain ⟨⟨y', hy'⟩, a', hab⟩ := exists_integer_multiple (submonoid.powers x) b,
  let m := (unique_factorization_monoid.normalized_factors a').count (normalize x),
  obtain ⟨d, hyd⟩ := (submonoid.mem_powers_iff y' x).mp hy',
  use a',
  use m,
  have := @unique_factorization_monoid.exists_associated_prime_pow_of_unique_normalized_factor,
  obtain ⟨a, y, c, no_factor, hca, hcy⟩ := 
    @unique_factorization_monoid.exists_reduced_factors' A _ _ a' y' _,
  
  -- obtain ⟨a', b', c', no_factor, rfl, rfl⟩ :=
  --   unique_factorization_monoid.exists_reduced_factors' a x _,
      -- (mem_non_zero_divisors_iff_ne_zero.mp y),
  obtain ⟨c'_nonzero, b'_nonzero⟩ := mul_mem_non_zero_divisors.mp b_nonzero,
  refine ⟨a', ⟨b', b'_nonzero⟩, @no_factor, _⟩,
  refine mul_left_cancel₀
    (is_fraction_ring.to_map_ne_zero_of_mem_non_zero_divisors b_nonzero) _,
  simp only [subtype.coe_mk, ring_hom.map_mul, algebra.smul_def] at *,
  erw [←hab, mul_assoc, mk'_spec' _ a' ⟨b', b'_nonzero⟩],
end

end away

end is_fraction_ring
