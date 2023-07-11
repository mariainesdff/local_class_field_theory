import discrete_valuation_ring.extensions
import number_theory.ramification_inertia

namespace discrete_valuation_ring

open valuation

variables {A : Type*} [comm_ring A] [is_domain A] [discrete_valuation_ring A]
-- We need to indicate in the doctring that h_alg is not an instance so when we apply it 
-- with local fields...
variables {B : Type*} [comm_ring B] [is_domain B] [discrete_valuation_ring B] (h_alg : algebra A B)

local notation `e(` B`,`A`)` := ideal.ramification_idx h_alg.to_ring_hom
  (local_ring.maximal_ideal A) (local_ring.maximal_ideal B)

lemma uniformizer_iff_unramified {a : A} (ha : is_uniformizer valued.v (↑a : fraction_ring A)) :
  is_uniformizer valued.v (↑(h_alg.to_ring_hom a) : fraction_ring B) ↔ e(B,A) = 1 :=
sorry

end discrete_valuation_ring