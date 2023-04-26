--import ring_theory.dedekind_domain.adic_valuation
import from_mathlib.rank_one_valuation
import from_mathlib.normed_valued
import topology.algebra.valued_field

open_locale discrete_valuation

namespace rank_one_valuation

variables {L : Type*} [field L] [valued L ℤₘ₀]

variables [hv: is_rank_one (@valued.v L _ ℤₘ₀ _ _)]
include hv 

--@[priority 100] instance : normed_field L := rank_one_valuation.valued_field.to_normed_field L ℤₘ₀

lemma norm_le_one_iff_val_le_one (x : L) :
  rank_one_valuation.norm_def x ≤ 1 ↔ valued.v x ≤ (1 : ℤₘ₀) :=
begin
  have hx : rank_one_valuation.norm_def x  = hv.hom (valued.v x) := rfl,
  rw [hx, ← nnreal.coe_one, nnreal.coe_le_coe, ← map_one  (is_rank_one.hom
      (@valued.v L _ ℤₘ₀ _ _)), strict_mono.le_iff_le],
  exact is_rank_one.strict_mono,
end

lemma norm_lt_one_iff_val_lt_one (x : L) :
  rank_one_valuation.norm_def x < 1 ↔ valued.v x < (1 : ℤₘ₀) :=
begin
  have hx : rank_one_valuation.norm_def x  = hv.hom (valued.v x) := rfl,
  rw [hx, ← nnreal.coe_one, nnreal.coe_lt_coe, ← map_one  (is_rank_one.hom
      (@valued.v L _ ℤₘ₀ _ _)), strict_mono.lt_iff_lt],
  exact is_rank_one.strict_mono,
end

lemma norm_pos_iff_val_pos (x : L) :
  0 < rank_one_valuation.norm_def x ↔ (0 : ℤₘ₀) < valued.v x :=
begin
  sorry
  /- have hx : rank_one_valuation.norm_def x  = hv.hom (valued.v x) := rfl,
  rw [hx, ← nnreal.coe_one, nnreal.coe_lt_coe, ← map_one  (is_rank_one.hom
      (@valued.v L _ ℤₘ₀ _ _)), strict_mono.lt_iff_lt],
  exact is_rank_one.strict_mono, -/
end

end rank_one_valuation

namespace rank_one_valuation

variables (L : Type*) [field L] (Γ₀ : Type*) [linear_ordered_comm_group_with_zero Γ₀]
  [val : valued L Γ₀] [hv : is_rank_one val.v]

include val hv

lemma norm_def_is_nonarchimedean : is_nonarchimedean (@norm_def L _ Γ₀ _ val hv) := 
norm_def_add_le

def mul_ring_norm_def : mul_ring_norm L :=
{ to_fun    := norm_def,
  map_zero' := by simp only [norm_def, map_zero, nonneg.coe_zero],
  add_le'   := λ x y, add_le_of_is_nonarchimedean norm_def_nonneg
                (norm_def_is_nonarchimedean L Γ₀) x y,
  neg'      := λ x, by simp only [norm_def, valuation.map_neg], 
  map_one'  := by simp only [norm_def, map_one, nonneg.coe_one],
  map_mul'  := λ x y, by simp only [norm_def, map_mul, nonneg.coe_mul],
  eq_zero_of_map_eq_zero' := λ x, norm_def_eq_zero }

end rank_one_valuation