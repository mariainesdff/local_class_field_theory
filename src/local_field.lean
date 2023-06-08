import eq_characteristic.valuation
import for_mathlib.residue_ring_def
import mixed_characteristic.valuation
import from_mathlib.rank_one_valuation


open valuation
open_locale discrete_valuation

class local_field (K : Type*) [field K] extends valued K ℤₘ₀ :=
(complete : complete_space K)
(is_discrete : is_discrete (@valued.v K _ ℤₘ₀ _ _))
(finite_residue_field : fintype (residue_ring K))

namespace mixed_char_local_field

--TODO: generalize is_discrete lemma to adic_valued completion
@[priority 100] noncomputable instance (p : out_param ℕ) [fact(nat.prime p)] (K : Type*) [field K] 
  [mixed_char_local_field p K] : local_field K := 
{ complete             := sorry,
  is_discrete          := 
  begin 
  have h : ∃ (π : (mixed_char_local_field.with_zero.valued K).v.integer), 
    discrete_valuation.is_uniformizer valued.v (π : K),
  { obtain ⟨π, hπ⟩ := is_dedekind_domain.height_one_spectrum.int_valuation_exists_uniformizer 
      (discrete_valuation.maximal_ideal valued.v.integer),
    have hcoe : algebra_map (mixed_char_local_field.with_zero.valued K).v.integer K π = (↑π : K) := 
    rfl,
    have hval : valued.v ((algebra_map ↥(valued.v.integer) K) π) =
      (discrete_valuation.maximal_ideal valued.v.integer).valuation 
        ((algebra_map ↥(valued.v.integer) K) π) := rfl,
    use π,
    rw discrete_valuation.is_uniformizer,
    rw ← hπ,
    rw ← hcoe, 
    rw is_dedekind_domain.height_one_spectrum.valuation_of_algebra_map,
    sorry, sorry, sorry,
    sorry },
    apply discrete_valuation.is_discrete_of_exists_uniformizer valued.v h.some_spec,

  end,
  finite_residue_field := sorry,
  ..(mixed_char_local_field.with_zero.valued K) }

end mixed_char_local_field

namespace eq_char_local_field

@[priority 100] noncomputable instance (p : out_param ℕ) [fact(nat.prime p)] (K : Type*) [field K]
  [eq_char_local_field p K] : local_field K := 
{ complete             := sorry,
  is_discrete          := sorry,
  finite_residue_field := sorry,
  ..(eq_char_local_field.with_zero.valued K) }

end eq_char_local_field

namespace local_field

end local_field