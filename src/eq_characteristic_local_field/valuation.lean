-- def normalized_valuation (K : Type*) [field K] [mixed_char_local_field p K] : valuation K ℤₘ₀ :=
--   (open_unit_ball K).valuation

-- instance (K : Type*) [field K] [mixed_char_local_field p K] : valued K ℤₘ₀ :=
--   valued.mk' (normalized_valuation K)