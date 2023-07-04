import field_theory.ratfunc
import ring_theory.dedekind_domain.adic_valuation

open is_dedekind_domain

noncomputable theory

open_locale classical discrete_valuation

namespace is_dedekind_domain.height_one_spectrum

variables {R : Type*} [comm_ring R] [is_domain R] [is_dedekind_domain R] {K : Type*} [field K]
  [algebra R K] [is_fraction_ring R K] (v : height_one_spectrum R)

lemma int_valuation_singleton {r : R} (hr : r ≠ 0) (hv : v.as_ideal = ideal.span {r}) : 
   v.int_valuation r = multiplicative.of_add (-1 : ℤ) :=
begin
  have h : v.int_valuation r = v.int_valuation_def r := rfl,
  rw [h, v.int_valuation_def_if_neg hr, ← hv, associates.count_self, algebra_map.coe_one],
  apply v.associates_irreducible, -- much faster than doing this inside the rw
end

end is_dedekind_domain.height_one_spectrum

variables (K : Type*) [field K]

noncomputable theory

open is_dedekind_domain.height_one_spectrum

namespace polynomial

def ideal_X : is_dedekind_domain.height_one_spectrum (polynomial K) := 
{ as_ideal := ideal.span({X}),
  is_prime := by { rw ideal.span_singleton_prime, exacts [prime_X, X_ne_zero] },
  ne_bot   := by { rw [ne.def, ideal.span_singleton_eq_bot], exact X_ne_zero }} 

@[simp]
lemma ideal_X_span : (ideal_X K).as_ideal = ideal.span({polynomial.X}) := rfl

lemma val_X_eq_one : 
  (ideal_X K).valuation (ratfunc.X : ratfunc K) = multiplicative.of_add (-1 : ℤ) :=
begin
  rw [← ratfunc.algebra_map_X, valuation_of_algebra_map, int_valuation_singleton],
  { exact X_ne_zero }, -- times out if within the rw (?)
  { exact ideal_X_span K }, --same (?)
end

end polynomial

namespace ratfunc

open polynomial

instance : valued (ratfunc K) ℤₘ₀ := valued.mk' (ideal_X K).valuation

lemma with_zero.valued_def {x : ratfunc K} :
  @valued.v (ratfunc K) _ _ _ (ratfunc.with_zero.valued K) x =(ideal_X K).valuation x := rfl 

end ratfunc
