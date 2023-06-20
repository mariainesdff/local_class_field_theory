import ring_theory.dedekind_domain.ideal

open unique_factorization_monoid

lemma count_normalized_factors_eq_count_normalized_factors_span {R : Type*} [comm_ring R]
  [is_domain R] [is_principal_ideal_ring R] [normalization_monoid R] [decidable_eq R] 
  [decidable_eq (ideal R)] {r X : R} (hr : r ≠ 0) 
  (hX₀ : X ≠ 0) (hX₁ : norm_unit X = 1) (hX : prime X) : 
  multiset.count X (normalized_factors r) =
    multiset.count (ideal.span {X} : ideal R ) (normalized_factors (ideal.span {r})) :=
begin
  classical,
  replace hX₁ : X = normalize X, 
  { simp only [normalize_apply, hX₁, units.coe_one, mul_one] },
  have : (ideal.span {normalize X} : ideal  R) = normalize (ideal.span {X}),
  { simp only [normalize_apply, normalize_eq],
    apply ideal.span_singleton_mul_right_unit (units.is_unit _) },
  rw [← part_enat.coe_inj, hX₁, ← multiplicity_eq_count_normalized_factors hX.irreducible hr, this, 
    ← multiplicity_eq_multiplicity_span, ← multiplicity_eq_count_normalized_factors],
  refine prime.irreducible (ideal.prime_of_is_prime _ _),
  { rwa [ne.def, ideal.span_singleton_eq_bot] },
  { rwa ideal.span_singleton_prime hX₀ },
  { rwa [ne.def, ideal.zero_eq_bot, ideal.span_singleton_eq_bot] },
end

open_locale classical --TODO: it would be better if we could put decidable instances instead

set_option profiler true
lemma count_normalized_factors_eq_associates_count 
  {R : Type*} [comm_ring R] [is_domain R] [is_dedekind_domain R]
  {I J : ideal R} (hI : I ≠ 0) (hJ : J.is_prime) (hJ₀ : J ≠ ⊥) :
  multiset.count J (normalized_factors I) = (associates.mk J).count (associates.mk I).factors :=
begin
  replace hI : associates.mk I ≠ 0,
  { apply associates.mk_ne_zero.mpr hI },
  have hJ' : irreducible (associates.mk J),
  { rw associates.irreducible_mk,
    apply prime.irreducible,
    apply ideal.prime_of_is_prime hJ₀ hJ },
  apply ideal.count_normalized_factors_eq,
  rw [← ideal.dvd_iff_le, ← associates.mk_dvd_mk, associates.mk_pow],
  rw associates.dvd_eq_le,
  rw associates.prime_pow_dvd_iff_le hI hJ',
  { rw ← ideal.dvd_iff_le,
    rw ← associates.mk_dvd_mk,
    rw associates.mk_pow,
    rw associates.dvd_eq_le,
    rw associates.prime_pow_dvd_iff_le hI hJ',
    linarith,
  },
end