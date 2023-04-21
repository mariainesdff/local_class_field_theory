import algebra.algebra.tower
import ring_theory.localization.fraction_ring

def algebra.comp (R A B : Type*) [comm_semiring R] [comm_semiring A] [comm_semiring B] 
  [algebra R A] [algebra A B] : algebra R B := 
(ring_hom.comp (algebra_map A B) (algebra_map R A)).to_algebra

lemma is_scalar_tower.comp (R A B : Type*) [comm_semiring R] [comm_semiring A] [comm_semiring B] 
  [algebra R A] [algebra A B] : 
  @is_scalar_tower R A B _ _ (algebra.comp R A B).to_has_smul :=
{ smul_assoc := λ r a b,
  begin
    letI : algebra R B := algebra.comp R A B,
    simp only [algebra.smul_def, map_mul, mul_assoc], refl, 
  end }

lemma is_scalar_tower.comp' (R A B S : Type*) [comm_semiring R]
  [comm_semiring A] 
  [comm_semiring B] [comm_semiring S] [algebra R A] [algebra A B] [algebra A S] [algebra B S] 
  [is_scalar_tower A B S] : 
    @is_scalar_tower R B S (algebra.comp R A B).to_has_smul _ (algebra.comp R A S).to_has_smul:=
{ smul_assoc := λ x y z,
  begin
    haveI := is_scalar_tower.comp R A B,
    haveI := is_scalar_tower.comp R A S,
    nth_rewrite 0 [← one_smul A y],
    rw [← one_smul A (y • z), ← smul_assoc, ← smul_assoc, ← smul_assoc],
  end }

lemma algebra_map_injective' (R A K : Type*) [comm_ring R] [field A] [algebra R A]
  [is_fraction_ring R A] [field K] [algebra R K] [algebra A K] [is_scalar_tower R A K] : 
  function.injective ⇑(algebra_map R K) :=
begin
  rw is_scalar_tower.algebra_map_eq R A K,
  exact function.injective.comp ((algebra_map A K).injective) (is_fraction_ring.injective R A)
end
