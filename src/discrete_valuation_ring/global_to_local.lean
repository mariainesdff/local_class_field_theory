/-
Copyright (c) 2023 María Inés de Frutos-Fernández, Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/

import ring_theory.dedekind_domain.adic_valuation
import discrete_valuation_ring.basic

namespace is_dedekind_domain.height_one_spectrum

open is_dedekind_domain is_dedekind_domain.height_one_spectrum valuation discrete_valuation
open_locale discrete_valuation

variables (R : Type*) [comm_ring R] [is_domain R] [is_dedekind_domain R]
  (K : Type*) [field K] [algebra R K] [is_fraction_ring R K]
  (v : height_one_spectrum R)

local notation `R_v` := is_dedekind_domain.height_one_spectrum.adic_completion_integers K v 
local notation `K_v` := is_dedekind_domain.height_one_spectrum.adic_completion K v

lemma valuation_completion_exists_uniformizer : 
  ∃ (π : K_v), valued.v π = (multiplicative.of_add ((-1 : ℤ))) :=
begin
  obtain ⟨x, hx⟩ := is_dedekind_domain.height_one_spectrum.valuation_exists_uniformizer K v,
  use ↑x,
  rw [is_dedekind_domain.height_one_spectrum.valued_adic_completion_def, ← hx, 
    valued.extension_extends],
  refl,
end

lemma valuation_completion_integers_exists_uniformizer : 
  ∃ (π : R_v), valued.v (π : K_v) = (multiplicative.of_add ((-1 : ℤ))) :=
begin 
  obtain ⟨x, hx⟩ := valuation_completion_exists_uniformizer R K v,
  refine ⟨⟨x, _⟩, hx⟩,
  rw [height_one_spectrum.mem_adic_completion_integers, hx],
  exact le_of_lt (with_zero.of_add_neg_one_lt_one)
end

instance : is_discrete (@valued.v K_v _ ℤₘ₀ _ _) := 
is_discrete_of_exists_uniformizer _
  (valuation_completion_integers_exists_uniformizer R K v).some_spec

instance : discrete_valuation_ring R_v :=
discrete_valuation.dvr_of_is_discrete (@valued.v K_v _ ℤₘ₀ _ _)


end is_dedekind_domain.height_one_spectrum