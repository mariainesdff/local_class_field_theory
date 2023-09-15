import discrete_valuation_ring.trivial_extension
import mixed_characteristic.basic

/-!
# The canonical valuation on a mixed characteristic local field

In this file we define the canonical valuation on a mixed characteristic local field, which is the
`discrete_valuation.extended_valuation` constructed from the `p`-adic valuation on `Q_p p`.

## Main Definitions
* `mixed_char_local_field.with_zero.valued` : the valued instance in a mixed characteristic local
  field, induced by the extension of the `p`-adic valuation.

##  Main Theorems
* `mixed_char_local_field.complete_space` : a mixed characteristic local field is a complete space. 

* `mixed_char_local_field.valuation.is_discrete` : the canonical valuation in a mixed characteristic 
  local field is discrete.

* `mixed_char_local_field.ring_of_integers.discrete_valuation_ring` : the ring of integers of a 
  mixed characteristic local field is a discrete valuation ring. 

## Implementation details
Note that when `K = Q_p p`, there are two valued instances on it : the one coming from the fact that
`Q_p p` is defined as the `adic_completion` of `ℚ` with respect to the ideal `(p)`, and the one
obtained by extending this valuation on `Q_p p` to its trivial field extension `Q_p p`.
These instances are mathematically equivalent, but not definitionally equal. However, the lemma
`discrete_valuation.extension.trivial_extension_eq_valuation` from the file 
`discrete_valuation_ring.trivial_extension` allow us to easily translate between the two instances
on `Q_p p`, whenever the diamond comes up.

-/

noncomputable theory

open discrete_valuation discrete_valuation.extension is_dedekind_domain multiplicative nnreal 
  padic_comparison padic_comparison.padic' polynomial multiplicative 
  is_dedekind_domain.height_one_spectrum

open_locale mixed_char_local_field nnreal discrete_valuation

variables (p : out_param (ℕ)) [hp : fact (p.prime)] 

include hp

namespace mixed_char_local_field

variables (K : Type*) [field K] [mixed_char_local_field p K]

/-- The valued instance in a mixed characteristic local field, induced by the extension of the 
  `p`-adic valuation. -/
@[priority 100] instance : valued K ℤₘ₀ := extension.valued (Q_p p) K

/-- A mixed characteristic local field is a complete space. -/
@[priority 100] instance : complete_space K := extension.complete_space (Q_p p) K

/-- The canonical valuation in a mixed characteristic local field is discrete. -/
instance : valuation.is_discrete (mixed_char_local_field.with_zero.valued p K).v := 
extension.is_discrete_of_finite (Q_p p) K

/-- The ring of integers of a mixed characteristic local field is a discrete valuation ring. -/
instance : discrete_valuation_ring (𝓞 p K) := 
integral_closure.discrete_valuation_ring_of_finite_extension (Q_p p) K

variable {p}

lemma valuation_p_ne_zero : valued.v (p : K) ≠ (0 : ℤₘ₀) :=
by simp only [ne.def, valuation.zero_iff, nat.cast_eq_zero, hp.1.ne_zero, not_false_iff]

/-- The ramification index of a mixed characteristic local field `K` is given by the 
  additive valuation of the element `(p : K)`. -/
def ramification_index (K : Type*) [field K] [mixed_char_local_field p K] : ℤ := 
-(with_zero.unzero (valuation_p_ne_zero K)).to_add

localized "notation (name := ramification_index)
  `e` := mixed_char_local_field.ramification_index" in mixed_char_local_field

variable (p)

lemma padic.mem_integers_iff (y : Q_p p) : y ∈ 𝓞 p (Q_p p) ↔ ‖ y ‖ ≤ 1 :=
begin
  rw [mem_ring_of_integers, is_integrally_closed.is_integral_iff, norm_le_one_iff_val_le_one],
  refine ⟨λ h, _, λ h, ⟨⟨y, h⟩, rfl⟩⟩,
  { obtain ⟨x, hx⟩ := h,
    rw [← hx, ← mem_adic_completion_integers],
    exact x.2, },
end

/-- The local field `Q_p p` is unramified. -/
lemma is_unramified_Q_p : e (Q_p p) = 1 :=
begin
  rw [ramification_index, neg_eq_iff_eq_neg, ← to_add_of_add (-1 : ℤ)],
  apply congr_arg,
  rw [← with_zero.coe_inj, ← padic'.valuation_p p, with_zero.coe_unzero,
    ← trivial_extension_eq_valuation (Q_p p)],
  refl,
end

/-- A ring equivalence between `Z_p p` and the valuation subring of `Q_p p` viewed as a mixed
  characteristic local field. -/
noncomputable! def padic'_int.equiv_valuation_subring : 
  Z_p p ≃+* ↥(mixed_char_local_field.with_zero.valued p (Q_p p)).v.valuation_subring := 
{ to_fun    := λ x,
  begin
    use x.1, 
    have heq : (mixed_char_local_field.with_zero.valued p (Q_p p)).v x.val =
        extended_valuation (Q_p p) (Q_p p) x.val, { refl },
    rw [valuation.mem_valuation_subring_iff, heq, trivial_extension_eq_valuation (Q_p p)],
    exact x.2,
  end,
  inv_fun   := λ x,
  begin
    use x.1, 
    rw [valuation.mem_valuation_subring_iff, ← trivial_extension_eq_valuation (Q_p p)],
    exact x.2,
  end,
  left_inv  := λ x, by simp only [subtype.val_eq_coe, set_like.eta],
  right_inv := λ x, by simp only [subtype.val_eq_coe, set_like.eta],
  map_mul'  := λ x y, by simp only [subtype.val_eq_coe, subring.coe_mul, mul_mem_class.mk_mul_mk],
  map_add'  := λ x y, by simp only [subtype.val_eq_coe, subring.coe_add, add_mem_class.mk_add_mk] }

variable {p}

lemma padic'_int.equiv_valuation_subring_comm :
  (algebra_map (mixed_char_local_field.with_zero.valued p (Q_p p)).v.valuation_subring K).comp 
    (padic'_int.equiv_valuation_subring p).to_ring_hom = algebra_map (Z_p p) K :=
rfl

end mixed_char_local_field