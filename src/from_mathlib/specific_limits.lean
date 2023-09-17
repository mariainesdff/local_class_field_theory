/-
Copyright (c) 2023 Filippo A. E. Nuccio. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Filippo A. E. Nuccio
-/

import analysis.specific_limits.basic

open nnreal filter
open_locale nnreal topology

lemma nnreal.lt_one_of_tendsto_pow_0 (a : ℝ≥0) (h : tendsto (λ n : ℕ, a^n) at_top (𝓝 0)) :
  a < 1 :=
begin
  by_cases ha₀ : a = 0,
  {rw ha₀, exact zero_lt_one,},
  { by_contradiction ha_le,
    rw not_lt at ha_le,
    by_cases ha : a = 1,
    { simp only [ha, one_pow] at h,
      exact zero_ne_one (tendsto_nhds_unique h tendsto_const_nhds) },
    { replace h : tendsto (λ n : ℕ, (a : ennreal) ^n) at_top (𝓝 0),
      { rw ← ennreal.coe_zero,
        simp_rw [← ennreal.coe_pow, ennreal.tendsto_coe],
        exact h, },
      set b : ennreal := ↑(a⁻¹) with hb,
      replace h : tendsto (λ n : ℕ, b ^ n) at_top (𝓝 ⊤),
      { rw [hb, ennreal.coe_inv ha₀],
        convert (@ennreal.tendsto_inv_iff ℕ at_top (λ n, (↑a) ^ n) 0).mpr h,
        { funext n, exact ennreal.inv_pow.symm, },
        { simp only [ennreal.inv_zero] }},
      have hb₁ : b < 1,
      { rw [hb, ← ennreal.coe_one, ennreal.coe_lt_coe],
        exact inv_lt_one (lt_of_le_of_ne ha_le (ne.symm ha)) },
      exact ennreal.zero_ne_top (tendsto_nhds_unique
        (ennreal.tendsto_pow_at_top_nhds_0_of_lt_1 hb₁) h)}},
  end