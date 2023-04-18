import ring_theory.witt_vector.discrete_valuation_ring
import ring_theory.valuation.valuation_ring
import topology.algebra.valuation
import topology.algebra.ring.basic
import topology.algebra.uniform_group
import ring_theory.ideal.quotient
import algebra.order.with_zero
import topology.algebra.nonarchimedean.adic_topology
import algebra.group.with_one.basic
import algebra.order.group.type_tags
import topology.uniform_space.cauchy
import algebra.order.monoid.to_mul_bot
import ring_theory.perfection

noncomputable theory

open_locale discrete_valuation
open_locale classical filter topology nnreal

open ideal nnreal ideal ideal.quotient

--there might be a problem with [uniform_space V]
variables (p : ℕ) [fact (nat.prime p)]
variables (V : Type*) [comm_ring V] [valued V ℝ≥0] --[uniform_space V] [topological_ring V] [complete_space V]

local notation `pV ` := (ideal.span ({p} : set V))

-- instance foo6 : with_ideal V := { I := pV }

-- instance foo7 : uniform_add_group V := infer_instance
-- begin
--   apply topological_ring.to_topological_add_group,
-- end

-- def s : V ⧸ pV →* V := sorry

-- lemma later (b : V ⧸ pV) : s p V (b^p) = (s p V b)^ p := sorry

-- lemma even_later : s p V 1 = 1 := sorry

-- lemma useful (b : V) : s p V (ideal.quotient.mk pV b) = b := sorry

-- variables (V Vbar : Type*) [comm_ring V] [comm_ring Vbar]
-- variable (π : V →+* Vbar) (h : function.surjective π)

local notation ` ℰ ` := ring.perfection (V ⧸ pV) p

instance foo : char_p (V ⧸ pV) p := sorry

#check @valued.v V _ _ _ _

lemma val_and_mem (hV : valuation.integer (@valued.v V _ _ _ _) = ⊤)
  (hp : valued.v (↑p : V) = (1/(p : ℝ≥0))) {x : V} :
  x ∈ pV ↔ valued.v x ≤ (1 / (p : ℝ≥0)) :=
begin
  split,
  { intro hx,
    obtain ⟨y, hy⟩ := mem_span_singleton'.mp hx,
    rw [← hy, valuation.map_mul],
    apply mul_le_mul,
    rw nnreal.coe_le_coe,
    { let y' : valued.v.integer,
      use y,
      rw hV,
      apply set.mem_univ y,
      use y'.2 },
    all_goals{simp [hp, zero_le]}, },
  intro hx,
  rw mem_span_singleton,
end

lemma star_board (hp : valued.v (↑p : V) = (1/(p : ℝ≥0))) (x : ℕ → V) (hx : ∀ n, (x (n+1))^p - (x n) ∈ pV) (n k : ℕ) : 
  valued.v ((x (n+k))^(p^k) - (x n)) < (1 : ℝ≥0) :=
begin
  induction k with k hk,
  { rw [add_zero, pow_zero, pow_one, sub_self, valuation.map_zero],
    exact zero_lt_one },
  { rw [sub_eq_sub_add_sub _ _ ((x (n + k)) ^(p^k))],
    apply lt_of_le_of_lt,
    apply valuation.map_add,
    apply max_lt hk,
    specialize hx (n+k),
    rw nat.succ_eq_add_one,
    suffices mem_pV : x (n + (k + 1)) ^ p ^ (k + 1) - x (n + k) ^ p ^ k ∈ pV,
    have : valued.v (x (n + (k + 1)) ^ p ^ (k + 1) - x (n + k) ^ p ^ k) ≤ (1 / (p : ℝ≥0)),
    apply val_and_mem p V mem_pV,
    sorry,
    convert_to (x (n + k + 1) ^ p - x (n + k))^(p^k) ∈ pV using 0,
    { rw eq_iff_iff,--useless?
      have Exy : ∃ y, (x (n + k + 1) ^ p - x (n + k))^(p^k) = x (n + (k + 1)) ^ p ^ (k + 1) -
        x (n + k) ^ p ^ k + p * y,
      { rw [sub_eq_add_neg, add_pow],
      sorry },
      obtain ⟨y, hy⟩ := Exy,
      rw hy,
      refine (ideal.add_mem_iff_left pV _).symm,
      apply mem_span_singleton'.mpr,
      rw mul_comm,
      use y },
   refine pow_mem_of_mem pV hx (p^k) (pow_pos (nat.prime.pos (fact.out _)) _),
  },
end

-- lemma cross_board_one (x y : V) (k : ℕ) (h : valued.v (x - y) ≤ 1/(p^k : ℝ≥0)) :
--   valued.v (x^p - y^p) ≤ 1/(p^(k+1) : ℝ≥0) :=
-- begin
--   induction k with k hk,
--   { 
    

--   },
  -- rw 
  -- obtain ⟨z, hz⟩ : ∃ z, (x ^ p - y ^ p) = (x -y )^p + p * z, sorry,
  -- rw hz,
  -- apply (valuation.map_add _ _ _).trans,

-- end

lemma cross_board_n (x y : V) (h : valued.v (x - y) ≤ 1/(p : ℝ≥0)) (n : ℕ) :
  valued.v (x^(p^n) - y^(p^n)) ≤ 1/(p^(n+1) : ℝ≥0) :=
begin
  induction n with n hn,
  {simpa using h},
  { rw [pow_succ', pow_mul, pow_mul, ← geom_sum₂_mul, pow_succ, valuation.map_mul,
    ← one_div_mul_one_div, nat.succ_eq_add_one],
    apply mul_le_mul _ hn (zero_le _) (zero_le _),
    suffices : ↑p ∣ (finset.range p).sum (λ (i : ℕ), (x ^ p ^ n) ^ i * (y ^ p ^ n) ^ (p - 1 - i)),
    { obtain ⟨z, hz⟩ := this,
      replace hz : (finset.range p).sum (λ (i : ℕ), (x ^ p ^ n) ^ i * (y ^ p ^ n) ^ (p - 1 - i)) ∈ pV,
      { rw hz,
      rw mem_span_singleton',
      use z,
      rwa mul_comm},
      apply val_and_mem p V hz,
      },
    -- refine mul_dvd_mul _ ih,
  -- let I : ideal R := span {p},
  let f : V →+* V ⧸ pV := mk pV,
  have hp : (p : V ⧸ pV) = 0,
  { rw [← map_nat_cast f, eq_zero_iff_mem, mem_span_singleton], },
  rw [← mem_span_singleton, ← ideal.quotient.eq] at h,
  rw [← mem_span_singleton, ← eq_zero_iff_mem, ring_hom.map_geom_sum₂,
      ring_hom.map_pow, ring_hom.map_pow, h, geom_sum₂_self, hp, zero_mul],
    



  }
  -- { rw nat.succ_eq_add_one,
  --   rw pow_add,
  --   rw pow_one,
  --   rw pow_mul,
  --   rw pow_mul,
  --   apply cross_board_one,
  --   exact hn },
end




lemma is_cauchy
  -- (H : filter.has_basis (@nhds V (@uniform_space.to_topological_space V _) (0 : V)) (λ n : ℕ, true)
    -- (λ n, ((pV^n : ideal V) : set V)))
  (x : ℕ → V) (hx : ∀ n, (x (n+1))^p - (x n) ∈ pV) : cauchy_seq (λ n, (x n)^(p^n)) :=
begin
  have := filter.has_basis.cauchy_seq_iff,
end
-- include p
-- lemma bar : topological_space V :=
-- begin
--   -- have : ideal.adic_topology pV ≤ @uniform_space.to_topological_space V _,

-- end

-- lemma foo : ideal.adic_topology pV := sorry

def φ (e : ℰ) (m : ℕ) : V :=
begin
  let r : ℕ → V := λ n, ((quotient.mk_surjective (perfection.coeff (V ⧸ pV) p (n+m) e)).some)^(p^n),
  have : cauchy_seq r,
  sorry,
  use (cauchy_seq_tendsto_of_complete this).some,
end

lemma frob (e : ℰ) (m : ℕ) : (φ p V e (m+1))^p = φ p V e m := sorry

lemma φ_add (e e' : ℰ) (m : ℕ) : (φ p V e m) = φ p V e m := sorry

def iso : ℰ ≃* monoid.perfection V p := sorry

lemma iso_add (e e' : ℰ) (m : ℕ) : filter.tendsto (λ n, ((φ p V e (n+m)) + (φ p V e' (n+m)))^(p^n))
  filter.at_top (𝓝 (φ p V (e + e') m)) := sorry

def θ : witt_vector p ℰ →+* V :=
{ to_fun := λ x, tsum (λ n : ℕ, ↑p^n * (φ p V (x.coeff n) n)),
  map_one' := sorry,
  map_mul' := sorry,
  map_zero' := sorry,
  map_add' := sorry }

theorem surjective_theta : function.surjective (θ p V) := sorry
