/-
Copyright (c) 2023 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import algebra.char_p.subring
import discrete_valuation_ring.complete
import for_mathlib.power_series_adic_completion
import for_mathlib.power_series
import for_mathlib.rank_one_valuation
import for_mathlib.ring_theory.valuation.algebra_instances
import ring_theory.dedekind_domain.adic_valuation

/-!
--TODO: Fix comments
# Equal characteristic local fields
This file defines a number field, the ring of integers corresponding to it and includes some
basic facts about the embeddings into an algebraic closed field.
## Main definitions
 - `eq_char_local_field` defines an equal characteristic local field as a finite dimensional
`𝔽_[p]⟮⟮X⟯⟯`-algebra for some prime number `p`.
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
  rank_one_valuation valuation_subring
variables (p : ℕ) [fact(nat.prime p)] 

notation (name := prime_galois_field)
  `𝔽_[` p `]` := galois_field p 1

instance : fintype (local_ring.residue_field (power_series 𝔽_[p])) :=
fintype.of_equiv _ (residue_field_of_power_series (𝔽_[p])).to_equiv.symm


@[reducible] def FpX_completion := (ideal_X 𝔽_[p]).adic_completion (ratfunc 𝔽_[p])

--local attribute [reducible] FpX_completion

notation (name := FpX_completion)
  `𝔽_[` p `]⟮⟮` X `⟯⟯` := FpX_completion p


@[reducible]
definition FpX_int_completion :=
(ideal_X 𝔽_[p]).adic_completion_integers (ratfunc 𝔽_[p])

notation (name := FpX_int_completion)
  `𝔽_[` p `]⟦` X `⟧` := FpX_int_completion p

instance ratfunc.char_p : char_p (ratfunc 𝔽_[p]) p := 
char_p_of_injective_algebra_map ((algebra_map 𝔽_[p] (ratfunc 𝔽_[p])).injective) p

namespace FpX_completion

variable {p}

-- localized "notation (name := FpX_completion) `𝔽_[` p `]⟮⟮` X `⟯⟯` := FpX_completion p" in FpX_completion

instance : has_coe (ratfunc 𝔽_[p]) 𝔽_[p]⟮⟮X⟯⟯ := ⟨algebra_map (ratfunc 𝔽_[p]) 𝔽_[p]⟮⟮X⟯⟯⟩

lemma algebra_map_eq_coe (f : ratfunc 𝔽_[p]) : 
  algebra_map (ratfunc 𝔽_[p]) 𝔽_[p]⟮⟮X⟯⟯ f = coe f := rfl

instance char_p : char_p 𝔽_[p]⟮⟮X⟯⟯ p := 
char_p_of_injective_algebra_map ((algebra_map (ratfunc (galois_field p 1)) 𝔽_[p]⟮⟮X⟯⟯).injective) p 

--I made this a def so that we can refer to it by this shorter name. Or we could make a
-- local notation for it?
def with_zero.valued : valued 𝔽_[p]⟮⟮X⟯⟯ ℤₘ₀ :=
height_one_spectrum.valued_adic_completion (ratfunc 𝔽_[p]) (ideal_X 𝔽_[p])

lemma valuation_X :
  valued.v ((algebra_map (ratfunc (galois_field p 1)) 𝔽_[p]⟮⟮X⟯⟯) X) = of_add (-1 : ℤ) :=
begin
  rw [valued_adic_completion_def],
  erw [FpX_completion.algebra_map_eq_coe, valued.extension_extends, val_X_eq_one],
end

lemma mem_FpX_int_completion {x : 𝔽_[p]⟮⟮X⟯⟯} : x ∈ 𝔽_[p]⟦X⟧ ↔ (valued.v x : ℤₘ₀) ≤ 1 := iff.rfl

lemma X_mem_FpX_int_completion : algebra_map (ratfunc 𝔽_[p]) _ X ∈ 𝔽_[p]⟦X⟧ :=
begin
  erw [FpX_completion.mem_FpX_int_completion, FpX_completion.valuation_X],
  rw [← with_zero.coe_one, with_zero.coe_le_coe, ← of_add_zero, of_add_le],
  linarith,
end

instance : inhabited 𝔽_[p]⟮⟮X⟯⟯ := ⟨(0 : 𝔽_[p]⟮⟮X⟯⟯)⟩

instance : is_rank_one (@FpX_completion.with_zero.valued p _).v :=
discrete_valuation.is_rank_one valued.v

instance : normed_field 𝔽_[p]⟮⟮X⟯⟯ := valued_field.to_normed_field 𝔽_[p]⟮⟮X⟯⟯ ℤₘ₀

lemma mem_FpX_int_completion' {x : FpX_completion p} :
  x ∈ FpX_int_completion p ↔ ‖ x ‖  ≤ 1 :=
by erw [FpX_completion.mem_FpX_int_completion, norm_le_one_iff_val_le_one]

variable (p)
-- Upgrade to (ratfunc Fp)-algebra iso
def isom_laurent : 𝔽_[p]⟮⟮X⟯⟯  ≃+* (laurent_series 𝔽_[p]) := 
completion_laurent_series.laurent_series_ring_equiv 𝔽_[p]

end FpX_completion

namespace FpX_int_completion

-- Upgrade to (ratfunc Fp)-algebra iso
noncomputable!
definition integers_equiv_power_series : (power_series 𝔽_[p]) ≃+* 𝔽_[p]⟦X⟧ :=
completion_laurent_series.power_series_ring_equiv 𝔽_[p]


noncomputable! lemma residue_field_power_series_card :
  fintype.card (local_ring.residue_field (power_series 𝔽_[p])) = p :=
begin
  convert fintype.of_equiv_card ((residue_field_of_power_series 𝔽_[p]).to_equiv.symm),
  rw [galois_field.card p 1 one_ne_zero, pow_one]
end

variable {p}
noncomputable!
lemma residue_field_card_eq_char :
  nat.card (local_ring.residue_field 𝔽_[p]⟦X⟧) = p :=
by simp only [← nat.card_congr (local_ring.residue_field.map_equiv
  (integers_equiv_power_series p)).to_equiv, nat.card_eq_fintype_card,
  residue_field_power_series_card p]

variable (p)
noncomputable!
instance : fintype (local_ring.residue_field (𝔽_[p]⟦X⟧)) :=
fintype.of_equiv _ (local_ring.residue_field.map_equiv (integers_equiv_power_series p)).to_equiv

noncomputable!
lemma residue_field_fintype_of_completion : fintype (local_ring.residue_field (𝔽_[p]⟦X⟧)) := 
  infer_instance

end FpX_int_completion

namespace FpX_completion
-- open_locale FpX_completion

lemma valuation_base_eq_char : 
  valuation.base 𝔽_[p]⟮⟮X⟯⟯ valued.v = p :=
begin
  rw [valuation.base, if_pos],
  { exact nat.cast_inj.mpr FpX_int_completion.residue_field_card_eq_char, },
  { erw FpX_int_completion.residue_field_card_eq_char, 
    exact (fact.out (nat.prime p)).one_lt },
end

end FpX_completion

namespace FpX_int_completion
-- open_locale FpX_completion

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

def X : 𝔽_[p]⟦X⟧ := ⟨algebra_map (ratfunc 𝔽_[p]) _ X, FpX_completion.X_mem_FpX_int_completion⟩

end FpX_int_completion

namespace FpX_completion
-- open_locale FpX_completion

def X := algebra_map 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯ (FpX_int_completion.X p)

lemma X_eq_coe : X p = ↑(@ratfunc.X 𝔽_[p] _ _) := rfl

lemma norm_X : ‖ X p ‖ = 1/(p : ℝ) :=
begin
  have hv : valued.v (X p) = multiplicative.of_add (-1 : ℤ),
  { rw [← val_X_eq_one 𝔽_[p], height_one_spectrum.valued_adic_completion_def,
      FpX_completion.X_eq_coe, valued.extension_extends], refl, },
  have hX : ‖X p‖ = is_rank_one.hom  _ (valued.v (X p)) := rfl,
  rw [hX, hv, discrete_valuation.is_rank_one_hom_def],
  simp only [of_add_neg, with_zero.coe_inv, map_inv₀, nonneg.coe_inv, one_div, inv_inj],
  simp only [ with_zero_mult_int_to_nnreal, with_zero_mult_int_to_nnreal_def, 
    monoid_with_zero_hom.coe_mk], 
  rw dif_neg,
  { simp only [with_zero.unzero_coe, to_add_of_add, zpow_one],
    rw valuation_base_eq_char,simp only [nnreal.coe_nat_cast], },
  { simp only [with_zero.coe_ne_zero, with_zero_mult_int_to_nnreal_strict_mono, not_false_iff] },
end

variable {p}

lemma norm_X_pos : 0 < ‖ X p ‖ :=
by rw [norm_X, one_div, inv_pos, nat.cast_pos]; exact (_inst_1.out).pos

lemma norm_X_lt_one : ‖ X p ‖ < 1 :=
by rw [norm_X, one_div]; exact inv_lt_one (nat.one_lt_cast.mpr (_inst_1.out).one_lt)

instance : nontrivially_normed_field 𝔽_[p]⟮⟮X⟯⟯ :=
{ non_trivial := begin
    use (X p)⁻¹,
    rw [norm_inv],
    exact one_lt_inv norm_X_pos norm_X_lt_one ,
  end,
  ..(by apply_instance: normed_field 𝔽_[p]⟮⟮X⟯⟯) }

lemma X_mem_int_completion : X p ∈ FpX_int_completion p :=
begin
  rw [mem_FpX_int_completion, ← norm_le_one_iff_val_le_one],
  exact le_of_lt norm_X_lt_one,
end

lemma norm_is_nonarchimedean : is_nonarchimedean (norm : 𝔽_[p]⟮⟮X⟯⟯ → ℝ) := 
norm_def_is_nonarchimedean _ _

end FpX_completion

namespace FpX_int_completion
-- open_locale FpX_completion

variables (p) 

lemma X_ne_zero : FpX_int_completion.X p ≠ 0 :=
begin
  have h0 : (0 : FpX_int_completion p) = ⟨(0 : FpX_completion p), subring.zero_mem _⟩,
  { refl },
  rw [FpX_int_completion.X, ne.def, h0, subtype.mk_eq_mk, _root_.map_eq_zero],
  exact ratfunc.X_ne_zero,
end

open completion_laurent_series

lemma norm_lt_one_iff_dvd (F : 𝔽_[p]⟦X⟧) : ‖(F : 𝔽_[p]⟮⟮X⟯⟯)‖ < 1 ↔ ((FpX_int_completion.X p) ∣ F) := 
begin
  have hF : ‖(F : 𝔽_[p]⟮⟮X⟯⟯)‖ = rank_one_valuation.norm_def (F : 𝔽_[p]⟮⟮X⟯⟯) := rfl,
  suffices : (valued.v (F : 𝔽_[p]⟮⟮X⟯⟯)) < (1 : ℤₘ₀) ↔ ((FpX_int_completion.X p) ∣ F),
  { rwa [hF, rank_one_valuation.norm_lt_one_iff_val_lt_one] },
  set f : 𝔽_[p]⟮⟮X⟯⟯ := ↑F with h_Ff,
  set g := (laurent_series_ring_equiv 𝔽_[p]) f with h_fg,
  have once : (laurent_series_ring_equiv 𝔽_[p]).symm g = f,--used only once?
  {rw [h_fg, ring_equiv.symm_apply_apply] },
  rw ← with_zero.coe_one,
  rw ← of_add_zero,
  rw ← neg_zero,
  refine ⟨λ h, _, λ h, _⟩,
  { replace h : valued.v g < ↑(of_add (- (0 : ℤ))),
    { rw ← valuation_compare,
      convert h, },
    obtain ⟨G, h_Gg⟩ := (val_le_of_add_neg_zero_iff_eq_coe 𝔽_[p] g).mp (le_of_lt h),
    rw ← h_Gg at h,
    replace h : valued.v ↑G ≤ ↑(of_add (-1 : ℤ)),
    { have := multiplicative.lt_succ_iff_le,
      sorry,
      -- rw ← to_add_lt at h,
      -- -- rw with_zero.unzero_coe
      -- rw to_add_of_add at h,
      
    },
    have := ((int_valuation_le_iff_coeff_zero_of_lt 𝔽_[p] G).mp h 0 zero_lt_one),
    rw [power_series.coeff_zero_eq_constant_coeff, ← power_series.X_dvd_iff] at this,
    obtain ⟨C, hC⟩ := dvd_iff_exists_eq_mul_left.mp this,
    refine dvd_of_mul_left_eq ⟨(laurent_series_ring_equiv 𝔽_[p]).symm C, _⟩ _,
    { erw [FpX_completion.mem_FpX_int_completion, valuation_compare, val_le_one_iff_eq_coe],
      use ⟨C, refl _⟩ },
    apply_fun (algebra_map 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯) using subtype.val_injective,
    apply_fun (laurent_series_ring_equiv 𝔽_[p]),
    erw [algebra_map_eq_coe, algebra_map_eq_coe, ← h_Ff, ← h_fg, ← h_Gg, map_mul, hC, 
      power_series.coe_mul, ring_equiv.apply_symm_apply, ← (coe_X_compare 𝔽_[p])],
    refl, },
  {sorry,},


end

-- #exit

--   set G := (power_series_ring_equiv 𝔽_[p]).symm F with h_GF,
--   set f : 𝔽_[p]⟮⟮X⟯⟯ := ↑F with h_Ff,
--   set g := (laurent_series_ring_equiv 𝔽_[p]) f with h_fg,
--   have h_Gg : g = G, sorry,
--   -- -- simp,
--   have uff : (laurent_series_ring_equiv 𝔽_[p]).symm g = f,
--   {rw [h_fg, ring_equiv.symm_apply_apply] },
--   have temp := valuation_compare 𝔽_[p] g,
--   rw ← with_zero.coe_one,
--   rw ← of_add_zero,
--   rw ← neg_zero,
--   -- rw temp,
--   refine ⟨λ h, _, λ h, _⟩,
--   { --rw ← with_zero.coe_one at h,
--     -- rw ← of_add_zero at h,
--     -- rw ← neg_zero at h,
--     replace h : valued.v (G : (laurent_series 𝔽_[p])) < ↑(of_add (- (0 : ℤ))),
--     { rw ← h_Gg,
--       rw ← temp,
--       convert h },
--     have := (completion_laurent_series.int_valuation_le_iff_coeff_zero_of_lt 𝔽_[p] G).mp
--       (le_of_lt h),
--     sorry },
--   { convert_to valued.v (G : (laurent_series 𝔽_[p])) < ↑(of_add (- (0 : ℤ))),
--     { rw ← h_Gg,
--       rw ← temp,
--       apply congr_arg,
--       convert uff.symm },
--     have := (completion_laurent_series.int_valuation_le_iff_coeff_zero_of_lt 𝔽_[p] G).mpr,
--     sorry,
--     sorry  },
--   }
-- end


end FpX_int_completion

--TODO: Which version to keep?
-- For instances and lemmas that only need `K` to be an `𝔽_[p]⟮⟮X⟯⟯`-algebra
namespace adic_algebra
-- open_locale FpX_completion

-- NOTE: The instances in this section are not found by infer_instance, but at least the
-- `by apply` is no longer needed.

variables {p} (K L : Type*) [field K] [algebra 𝔽_[p]⟮⟮X⟯⟯ K] [field L] [algebra 𝔽_[p]⟮⟮X⟯⟯ L]

instance to_int_algebra : algebra 𝔽_[p]⟦X⟧ K := valuation_subring.algebra' _ K

@[simp] lemma int_algebra_map_def : algebra_map 𝔽_[p]⟦X⟧ K = 
  (adic_algebra.to_int_algebra K).to_ring_hom := rfl 

@[priority 10000] instance : is_scalar_tower 𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯ K :=
valuation_subring.is_scalar_tower _ _

@[priority 1000] instance int_is_scalar_tower [algebra K L] [is_scalar_tower 𝔽_[p]⟮⟮X⟯⟯ K L] :
  is_scalar_tower 𝔽_[p]⟦X⟧ K L :=
valuation_subring.int_is_scalar_tower _ K L

lemma algebra_map_injective : function.injective ⇑(algebra_map 𝔽_[p]⟦X⟧ L) :=
valuation_subring.algebra_map_injective _ L

end adic_algebra

-- open_locale FpX_completion

variable (p)

-- #where
/-- An equal characteristic local field is a field which is finite
dimensional over `𝔽_p((X))`, for some prime `p`. -/
class eq_char_local_field (p : out_param(ℕ)) [fact(nat.prime p)] (K : Type*) [field K] 
  extends algebra 𝔽_[p]⟮⟮X⟯⟯ K :=
[to_finite_dimensional : finite_dimensional 𝔽_[p]⟮⟮X⟯⟯ K]

-- #check eq_char_local_field p

attribute [priority 100, instance] eq_char_local_field.to_finite_dimensional

namespace eq_char_local_field

variables (p) (K L : Type*) [field K] [eq_char_local_field p K] [field L] [eq_char_local_field p L]

@[priority 100] instance char_p : char_p K p := 
char_p_of_injective_algebra_map (algebra_map 𝔽_[p]⟮⟮X⟯⟯ K).injective p

/-- The ring of integers of an equal characteristic local field is the integral closure of 𝔽_[p]⟦X⟧
  in the local field. -/
def ring_of_integers := integral_closure 𝔽_[p]⟦X⟧ K

localized "notation (name := ring_of_integers)
  `𝓞` := eq_char_local_field.ring_of_integers" in eq_char_local_field

lemma mem_ring_of_integers (x : K) : x ∈ 𝓞 p K ↔ is_integral 𝔽_[p]⟦X⟧ x := iff.rfl

-- TODO: Delete? Has been generalized.
lemma is_integral_of_mem_ring_of_integers {x : K} (hx : x ∈ 𝓞 p K) :
  is_integral 𝔽_[p]⟦X⟧ (⟨x, hx⟩ : 𝓞 p K) :=
is_integral_of_mem_ring_of_integers _ K _

/-- Given an algebra between two local fields over 𝔽_[p]⟮⟮X⟯⟯, create an algebra between their two
  rings of integers. For now, this is not an instance by default as it creates an
  equal-but-not-defeq diamond with `algebra.id` when `K = L`. This is caused by `x = ⟨x, x.prop⟩`
  not being defeq on subtypes. This will likely change in Lean 4. -/
def ring_of_integers_algebra [algebra K L] [is_scalar_tower 𝔽_[p]⟮⟮X⟯⟯ K L] :
  algebra (𝓞 p K) (𝓞 p L) := 
valuation_subring.valuation_subring_algebra _ K L

namespace ring_of_integers

variables {K}

-- Making FpX_int_completion.is_fraction_ring explicit speeds out the proof
instance : is_fraction_ring (𝓞 p K) K := 
@integral_closure.is_fraction_ring_of_finite_extension 
  𝔽_[p]⟦X⟧ 𝔽_[p]⟮⟮X⟯⟯ _ _ K _ _ _ FpX_int_completion.is_fraction_ring _ _ _ _

instance : is_integral_closure (𝓞 p K) 𝔽_[p]⟦X⟧ K := integral_closure.is_integral_closure _ _

-- These two instances speed up the proof of `equiv` a bit.
instance : algebra 𝔽_[p]⟦X⟧ (𝓞 p K) := infer_instance

instance : is_scalar_tower 𝔽_[p]⟦X⟧ (𝓞 p K) K := infer_instance

lemma is_integral_coe (x : 𝓞 p K) : is_integral 𝔽_[p]⟦X⟧ (x : K) := x.2

/-- The ring of integers of `K` is equivalent to any integral closure of `𝔽_[p]⟦X⟧` in `K` -/
-- TODO: go back to old proof?
protected noncomputable! def equiv (R : Type*) [comm_ring R] [algebra 𝔽_[p]⟦X⟧ R] [algebra R K]
  [is_scalar_tower 𝔽_[p]⟦X⟧ R K] [is_integral_closure R 𝔽_[p]⟦X⟧ K] : 𝓞 p K ≃+* R :=
begin
  letI : algebra (valued.v.valuation_subring ) R := _inst_7,
  letI : is_integral_closure R ↥(valued.v.valuation_subring) K := _inst_10,
  letI : is_scalar_tower ↥(valued.v.valuation_subring) R K := _inst_9,
  exact valuation_subring.equiv _ K R,
end

variables (K)

instance : char_p (𝓞 p K) p := char_p.subring' K p (𝓞 p K).to_subring

lemma algebra_map_injective :
  function.injective ⇑(algebra_map 𝔽_[p]⟦X⟧ (ring_of_integers p K)) := 
valuation_subring.integral_closure_algebra_map_injective _ K

end ring_of_integers

end eq_char_local_field

namespace FpX_completion

open eq_char_local_field

open_locale eq_char_local_field

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
  have h1 := FpX_int_completion.FpX_completion.is_integral_closure p,
  exact @h h1,
end

lemma open_unit_ball_def : 
  local_ring.maximal_ideal 𝔽_[p]⟦X⟧ = ideal.span {FpX_int_completion.X p} :=
by apply discrete_valuation.is_uniformizer_is_generator; exact valuation_X

end FpX_completion

namespace FpX_int_completion

variables (K : Type*) [field K] [eq_char_local_field p K]

open eq_char_local_field
open_locale eq_char_local_field

lemma X_coe_ne_zero : ¬(algebra_map (FpX_int_completion p) (𝓞 p K)) (FpX_int_completion.X p) = 0 :=
begin
  intro h,
  exact FpX_int_completion.X_ne_zero p
    ((injective_iff_map_eq_zero _).mp (ring_of_integers.algebra_map_injective p K) _ h),
end

instance : algebra (ratfunc 𝔽_[p]) K := 
(ring_hom.comp (algebra_map 𝔽_[p]⟮⟮X⟯⟯ K) (algebra_map (ratfunc 𝔽_[p]) 𝔽_[p]⟮⟮X⟯⟯)).to_algebra

end FpX_int_completion
