import discrete_valuation_ring.trivial_extension
import eq_characteristic.basic

/-!
# The canonical valuation on an equal characteristic local field

In this file we define the canonical valuation on an equal characteristic local field, which is the
`discrete_valuation.extended_valuation` constructed from the `X`-adic valuation on `FpX_completion`.

## Main Definitions
* `eq_char_local_field.with_zero.valued` : the valued instance in an equal characteristic local
  field, induced by the extension of the `X`-adic valuation.

##  Main Theorems
* `eq_char_local_field.complete_space` : an equal characteristic local field is a complete space. 

* `eq_char_local_field.valuation.is_discrete` : the canonical valuation in an equal characteristic 
  local field is discrete.

* `eq_char_local_field.ring_of_integers.discrete_valuation_ring` : the ring of integers of an 
  equal characteristic local field is a discrete valuation ring. 

## Implementation details
Note that when `K = FpX_completion`, there are two valued instances on it : the one coming from the
fact that `FpX_completion` is defined as the `adic_completion` of `ratfunc 𝔽_[p]` with respect to
the ideal `(X)`, and the one obtained by extending this valuation on `FpX_completion` to its trivial
field extension `FpX_completion`. These instances are mathematically equivalent, but not
definitionally equal. However `discrete_valuation.extension.trivial_extension_eq_valuation` from the
file `discrete_valuation_ring.trivial_extension` allow us to easily translate between the two
instances on `FpX_completion`, whenever this diamond comes up.

-/

noncomputable theory

open discrete_valuation is_dedekind_domain multiplicative nnreal polynomial ratfunc
  discrete_valuation.extension
open_locale eq_char_local_field nnreal discrete_valuation

namespace eq_char_local_field

variables (p : out_param (ℕ)) [hp : fact (p.prime)] 

include hp
variables (K : Type*) [field K] [eq_char_local_field p K]

/-- The valued instance in an equal characteristic local field, induced by the extension of the 
  `X`-adic valuation.-/
@[priority 100] instance : valued K ℤₘ₀ := extension.valued (FpX_completion p) K

/-- An equal characteristic local field is a complete space. -/
@[priority 100] instance : complete_space K := extension.complete_space (FpX_completion p) K

/-- The canonical valuation in an equal characteristic local field is discrete. -/
instance : valuation.is_discrete (eq_char_local_field.with_zero.valued p K).v := 
extension.is_discrete_of_finite (FpX_completion p) K

/-- The ring of integers of an equal characteristic local field is a discrete valuation ring. -/
instance : discrete_valuation_ring (𝓞 p K) := 
integral_closure.discrete_valuation_ring_of_finite_extension (FpX_completion p) K

variables {p}

lemma valuation_X_ne_zero : valued.v (algebra_map (ratfunc 𝔽_[p]) K X) ≠ (0 : ℤₘ₀) :=
by simp only [ne.def, _root_.map_eq_zero, ratfunc.X_ne_zero, not_false_iff] 

/-- The ramification index of an equal characteristic local field `K` is given by the 
  additive valuation of the element `(X : K)`. -/
def ramification_index (K : Type*) [field K] [eq_char_local_field p K] : ℤ := 
  -(with_zero.unzero (valuation_X_ne_zero K)).to_add

localized "notation (name := ramification_index)
  `e` := eq_char_local_field.ramification_index" in eq_char_local_field 

variables (p)

/-- The local field `FpX_completion` is unramified. -/
lemma is_unramified_FpX_completion : e (FpX_completion p) = 1 := 
begin
  have hX : (eq_char_local_field.with_zero.valued p (FpX_completion p)).v (FpX_completion.X p) = 
    (of_add (-1 : ℤ)),
  { have heq : (eq_char_local_field.with_zero.valued p (FpX_completion p)).v =
    extended_valuation (FpX_completion p) (FpX_completion p),
    { refl },
    rw [← @FpX_completion.valuation_X p _, FpX_completion.X, FpX_int_completion.X,
      eq_char_local_field.with_zero.valued, heq,
      discrete_valuation.extension.trivial_extension_eq_valuation],
    refl },
  rw [ramification_index, neg_eq_iff_eq_neg, ← to_add_of_add (-1 : ℤ)],
  apply congr_arg,
  rw [← with_zero.coe_inj, ← hX, with_zero.coe_unzero],
  refl,
end

/-- A ring equivalence between `FpX_int_completion` and the valuation subring of `FpX_completion`
viewed as an equal characteristic local field. -/
noncomputable! def FpX_int_completion.equiv_valuation_subring : (FpX_int_completion p) ≃+* 
  ↥(eq_char_local_field.with_zero.valued p (FpX_completion p)).v.valuation_subring := 
{ to_fun    := λ x,
  begin
    use x.1, 
    have heq : (eq_char_local_field.with_zero.valued p (FpX_completion p)).v x.val =
        extended_valuation (FpX_completion p) (FpX_completion p) x.val, { refl },
    rw [valuation.mem_valuation_subring_iff, heq, trivial_extension_eq_valuation
      (FpX_completion p)],
    exact x.2,
  end,
  inv_fun   := λ x,
  begin
    use x.1,
    rw [FpX_int_completion, height_one_spectrum.mem_adic_completion_integers,
      ← trivial_extension_eq_valuation (FpX_completion p)],
    exact x.2
  end,
  left_inv  := λ x, by simp only [subtype.val_eq_coe, set_like.eta],
  right_inv := λ x, by simp only [subtype.val_eq_coe, set_like.eta],
  map_mul'  := λ x y, by simp only [subtype.val_eq_coe, subring.coe_mul, mul_mem_class.mk_mul_mk],
  map_add'  := λ x y, by simp only [subtype.val_eq_coe, subring.coe_add, add_mem_class.mk_add_mk] }

variable {p}

lemma FpX_int_completion.equiv_valuation_subring_comm :
  (algebra_map (eq_char_local_field.with_zero.valued p
    (FpX_completion p)).v.valuation_subring K).comp
      (FpX_int_completion.equiv_valuation_subring p).to_ring_hom = 
  algebra_map (FpX_int_completion p) K :=
rfl

end eq_char_local_field