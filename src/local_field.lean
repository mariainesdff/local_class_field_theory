import eq_characteristic_local_field.basic
import for_mathlib.residue_ring_def
import mixed_characteristic.valuation

namespace local_field

open valuation
open_locale discrete_valuation

class local_field (K : Type*) [field K] extends valued K ℤₘ₀ :=
(finite_residue_field : fintype (residue_ring K) )


end local_field
