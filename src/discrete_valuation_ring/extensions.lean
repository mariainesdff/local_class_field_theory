import discrete_valuation_ring.basic

open valuation
open_locale discrete_valuation

section complete

variables (K : Type*) [field K] [hv : valued K ℤₘ₀] [is_discrete hv.v] 
 -- [hu : uniform_space K]
include hv
--  example : uniform_space K := infer_instance

-- Without finite_dimensional, the fails_quickly does not complain
variables (L : Type*) [field L] [algebra K L] [complete_space K] -- [finite_dimensional K L]
-- 


--  example : uniform_space K := infer_instance
--instance [finite_dimensional K L] : uniform_space L := infer_instance
--instance normed_L : normed_field L := sorry
def w : valuation L ℤₘ₀ := sorry -- May be a bit hard

-- instance : is_discrete w :=
--is it reasonable to first have the `def` and then this `instance`?
--instance : valued L ℤₘ₀ := hw K L

--#lint

--TODO: fix
--instance : complete_space L := sorry

--instance is_discrete_of_finite : is_discrete (@valued.v L _ ℤₘ₀ _ _) := sorry
instance is_discrete_of_finite : is_discrete (w K L) := sorry

/- lemma integral_closure_eq_integer :
  (integral_closure hv.v.integer L).to_subring = (@valued.v L _ ℤₘ₀ _ _).integer :=
sorry -/
lemma integral_closure_eq_integer :
  (integral_closure hv.v.integer L).to_subring = (w K L).integer :=
sorry

--Chapter 2, Section 2, Proposition 3 in Serre's Local Fields
lemma dvr_of_finite_extension : discrete_valuation_ring (integral_closure hv.v.integer L) := sorry
-- proof: make a local instance of valued on `L`

lemma integral_closure_finrank :
  finite_dimensional.finrank hv.v.integer (integral_closure hv.v.integer L) =
  finite_dimensional.finrank K L :=
sorry

local notation `K₀` := hv.v.integer

local notation `L₀` := (w K L).integer

def integer.algebra : algebra K₀ L₀ :=
by rw ← integral_closure_eq_integer; exact (integral_closure ↥(valued.v.integer) L).algebra

end complete

section unramified

open discrete_valuation

variables {A : Type*} [comm_ring A] [is_domain A] [discrete_valuation_ring A]

lemma is_domain_of_irreducible {f : polynomial A} 
  (hf : irreducible (polynomial.map (algebra_map A (local_ring.residue_field A)) f)) :
  is_domain (adjoin_root f) :=
sorry

-- Ch. I, Section 6, Prop. 15 of Serre's "Local Fields"
lemma is_dvr_of_irreducible {f : polynomial A} 
  (hf : irreducible (polynomial.map (algebra_map A (local_ring.residue_field A)) f)) :
  @discrete_valuation_ring (adjoin_root f) _ (is_domain_of_irreducible hf) :=
sorry

-- Ch. I, Section 6, Cor. 1 of Serre's "Local Fields"
lemma is_dvr_of_irreducible' {f : polynomial A} 
  (hf : irreducible (polynomial.map (algebra_map A (local_ring.residue_field A)) f)) :
  is_integral_closure (adjoin_root f) A (fraction_ring (adjoin_root f)) :=
sorry

local notation `K` := fraction_ring A

variables (L : Type*) [field L] [algebra K L] [finite_dimensional K L] [algebra A L]
[is_scalar_tower A K L]

open finite_dimensional

--Serre's Proposition 16 in Chapter I, Section 6: we may want the algebra instance to become an\
-- explicit variable so that when we use the definition we do not need `@`.
noncomputable!
def minimal_poly_eq_residue_fields_of_unramified
  (hB : discrete_valuation_ring (integral_closure A L))
  [algebra (local_ring.residue_field A)
  (@local_ring.residue_field _ _ hB.to_local_ring)]
  (hpb : power_basis (local_ring.residue_field A)
  (@local_ring.residue_field _ _ hB.to_local_ring))
  (hdeg : finrank K L = hpb.dim) (x : (integral_closure A L))
  (hx : ideal.quotient.mk (@local_ring.maximal_ideal _ _ hB.to_local_ring) x = hpb.gen) : 
  (integral_closure A L) ≃+* algebra.adjoin A ({x} : set (integral_closure A L)) := sorry

noncomputable!
def minimal_poly_eq_residue_fields_of_unramified'
  (hB : discrete_valuation_ring (integral_closure A L))
  [algebra (local_ring.residue_field A)
  (@local_ring.residue_field _ _ hB.to_local_ring)]
  (hpb : power_basis (local_ring.residue_field A)
  (@local_ring.residue_field _ _ hB.to_local_ring))
  (hdeg : finrank K L = hpb.dim) (x : (integral_closure A L))
  (hx : ideal.quotient.mk (@local_ring.maximal_ideal _ _ hB.to_local_ring) x = hpb.gen) : 
  (integral_closure A L) ≃+* adjoin_root (minpoly A x) := sorry



/- variables (K : Type*) [field K] [hv : valued K ℤₘ₀] [is_discrete hv.v]
variables (L : Type*) [field L] [hw : valued L ℤₘ₀] [is_discrete hw.v]
variables 

include hv hw
/- postfix `₀`:1025:= valued.v.integer

#check K₀ -/
local notation `K₀` := hv.v.integer

local notation `L₀` := hw.v.integer -/

--variable (hmax : algebra_map )

-- We need to indicate in the doctring that h_alg is not an instance so when we apply it with local fields...
variables {B : Type*} [comm_ring B] [is_domain B] [discrete_valuation_ring B] (h_alg : algebra A B)

local notation `e(` B`,`A`)` := ideal.ramification_idx h_alg.to_ring_hom
  (local_ring.maximal_ideal A) (local_ring.maximal_ideal B)

lemma uniformizer_iff_unramified {a : A} (ha : is_uniformizer (↑a : fraction_ring A)) :
  is_uniformizer (↑(h_alg.to_ring_hom a) : fraction_ring B) ↔ e(B,A) = 1 :=
sorry

end unramified
