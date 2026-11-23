import Formalism.HermitianCurvature.StatementWd

namespace Formalism.FourierDecayAlt.P.Wd3

open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd

section

variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A]
  [Fintype S] [DecidableEq S]

theorem eU_mul (a : S) (i j k l : Fin 2) :
    (eU a i j : SlopeTestRemainingChoices S A) * eU a k l = if j = k then eU a i l else 0 := by
  ext x y
  rw [Matrix.mul_apply, Finset.sum_eq_single (Function.update x a j)]
  · by_cases hjk : j = k
    · subst hjk
      rw [if_pos rfl]
      simp only [eU, Matrix.of_apply]
      by_cases hx : x a = i <;> by_cases hy : y a = l <;> by_cases hxy : ∀ b, b ≠ a → x b = y b <;>
        simp (config := {contextual := true}) [Function.update_apply, hx, hy, hxy]
    · rw [if_neg hjk]
      simp [eU, Function.update_apply, hjk]
  · intro z _ hz
    simp only [eU, Matrix.of_apply]
    rw [if_neg, zero_mul]
    rintro ⟨_, h2, h3⟩
    apply hz
    funext b
    by_cases hb : b = a
    · subst hb
      simp [h2]
    · rw [Function.update_of_ne hb]
      exact (h3 b hb).symm
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem mul_ins (a : S) (m : SlopeTestRemainingChoices S A) (N : M2 (SlopeTestRemainingChoices S A)) (hm : FreeOf a m) :
    m * ins a N = ∑ r, ∑ s, eU a r s * (m * N r s) := by
  have hm' : ∀ i j, Commute (eU a i j) m := hm
  rw [ins, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← mul_assoc, ← (hm' r s).eq, mul_assoc]

theorem ins_mul (a : S) (m : SlopeTestRemainingChoices S A) (N : M2 (SlopeTestRemainingChoices S A)) :
    ins a N * m = ∑ r, ∑ s, eU a r s * (N r s * m) := by
  rw [ins, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mul_assoc]

theorem eU_mul_ins (a : S) (k i : Fin 2) (m : SlopeTestRemainingChoices S A) (N : M2 (SlopeTestRemainingChoices S A)) (hm : FreeOf a m) :
    eU a k i * m * ins a N = ∑ s, eU a k s * (m * N i s) := by
  rw [mul_assoc, mul_ins a m N hm, Finset.mul_sum, Finset.sum_eq_single i]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← mul_assoc, eU_mul, if_pos rfl]
  · intro r _ hr
    rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [← mul_assoc, eU_mul, if_neg (Ne.symm hr), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem ins_mul_eU (a : S) (j k : Fin 2) (m : SlopeTestRemainingChoices S A) (N : M2 (SlopeTestRemainingChoices S A)) (hm : FreeOf a m)
    (hN : FreeOf2 a N) :
    ins a N * (m * eU a j k) = ∑ r, eU a r k * (N r j * m) := by
  have hm' : ∀ i j, Commute (eU a i j) m := hm
  have h1 : ∀ r s, FreeOf a (N r s) := hN
  have hN' : ∀ r s i j, Commute (eU a i j) (N r s) := fun r s => h1 r s
  rw [← mul_assoc, ins_mul a m N, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_mul, Finset.sum_eq_single j]
  · have hc : Commute (eU a j k) (N r j * m) := (hN' r j j k).mul_right (hm' j k)
    rw [mul_assoc, ← hc.eq, ← mul_assoc, eU_mul, if_pos rfl]
  · intro s _ hs
    have hc : Commute (eU a j k) (N r s * m) := (hN' r s j k).mul_right (hm' j k)
    rw [mul_assoc, ← hc.eq, ← mul_assoc, eU_mul, if_neg hs, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem firstEmbed_mul_secondEmbed_apply {B : Type} [Ring B] (M N : M2 B) (i r j s : Fin 2) :
    (E1 M * E2 N) (i, r) (j, s) = M i j * N r s := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp [E1, E2, ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem secondEmbed_mul_firstEmbed_apply {B : Type} [Ring B] (M N : M2 B) (i r j s : Fin 2) :
    (E2 N * E1 M) (i, r) (j, s) = N r s * M i j := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp [E1, E2, ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem Pf_mul {B : Type} [Ring B] (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) (i r : Fin 2)
    (y : Fin 2 × Fin 2) : (Pf B * X) (i, r) y = X (r, i) y := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp [Pf, ite_and, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem mul_Pf {B : Type} [Ring B] (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) (j s : Fin 2)
    (x : Fin 2 × Fin 2) : (X * Pf B) x (j, s) = X x (s, j) := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp [Pf, ite_and, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem rtt_entry {B : Type} [Ring B] [Algebra K B] (M N : M2 B) (D : K)
    (h : (D • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) - Pf B) * E1 M * E2 N =
      E2 N * E1 M * (D • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) - Pf B))
    (i r j s : Fin 2) :
    D • (M i j * N r s) - M r j * N i s = D • (N r s * M i j) - N r j * M i s := by
  have h' := congrFun (congrFun h (i, r)) (j, s)
  rw [mul_assoc, sub_mul, Matrix.smul_mul, Matrix.one_mul, mul_sub, Matrix.mul_smul, Matrix.mul_one] at h'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Pf_mul, mul_Pf, firstEmbed_mul_secondEmbed_apply, secondEmbed_mul_firstEmbed_apply] at h'
  exact h'

theorem plus_core (a : S) (M N : M2 (SlopeTestRemainingChoices S A)) (D : K) (hM : FreeOf2 a M) (hN : FreeOf2 a N)
    (h : ∀ i r j s, D • (M i j * N r s) - M r j * N i s = D • (N r s * M i j) - N r j * M i s) :
    (D • (1 : M2 (SlopeTestRemainingChoices S A)) - P0 a) * M * d0 (ins a N) =
      d0 (ins a N) * M * (D • (1 : M2 (SlopeTestRemainingChoices S A)) - P0 a) := by
  have hM' : ∀ i j, FreeOf a (M i j) := hM
  refine Matrix.ext fun i j => ?_
  have key : ∀ r s, D • (eU a r s * (M i j * N r s)) - eU a r s * (M r j * N i s) =
      D • (eU a r s * (N r s * M i j)) - eU a r s * (N r j * M i s) := fun r s => by
    have := congrArg (eU a r s * ·) (h i r j s)
    simp only [mul_sub, mul_smul_comm] at this
    exact this
  have hL : (((D • (1 : M2 (SlopeTestRemainingChoices S A)) - P0 a) * M * d0 (ins a N) : M2 (SlopeTestRemainingChoices S A))) i j =
      D • (M i j * ins a N) - ∑ k, eU a k i * M k j * ins a N := by
    rw [sub_mul, sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.sub_apply,
      Matrix.smul_apply, d0, Matrix.mul_diagonal, Matrix.mul_diagonal, Matrix.mul_apply, Finset.sum_mul]
    rfl
  have hR : ((d0 (ins a N) * M * (D • (1 : M2 (SlopeTestRemainingChoices S A)) - P0 a) : M2 (SlopeTestRemainingChoices S A))) i j =
      D • (ins a N * M i j) - ∑ k, ins a N * (M i k * eU a j k) := by
    rw [mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.sub_apply, Matrix.smul_apply, d0,
      Matrix.diagonal_mul, Matrix.mul_apply]
    simp only [Matrix.diagonal_mul, mul_assoc]
    rfl
  rw [hL, hR, mul_ins a _ N (hM' i j), ins_mul,
    Finset.sum_congr rfl fun k _ => eU_mul_ins a k i (M k j) N (hM' k j),
    Finset.sum_congr rfl fun k _ => ins_mul_eU a j k (M i k) N (hM' i k) hN,
    Finset.sum_comm (f := fun k r => eU a r k * (N r j * M i k)),
    Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => key r s

theorem minus_core (b : S) (M N : M2 (SlopeTestRemainingChoices S A)) (d : K) (hM : FreeOf2 b M) (hN : FreeOf2 b N)
    (h : ∀ i r j s, d • (N i j * M r s) - N r j * M i s = d • (M r s * N i j) - M r j * N i s) :
    d0 (ins b Nᵀ) * (d • (1 : M2 (SlopeTestRemainingChoices S A)) - Q0 b) * M =
      M * (d • (1 : M2 (SlopeTestRemainingChoices S A)) - Q0 b) * d0 (ins b Nᵀ) := by
  have hM' : ∀ i j, FreeOf b (M i j) := hM
  have hC : ∀ i j k l, Commute (eU b k l) (M i j) := fun i j => hM' i j
  have h1 : ∀ r s, FreeOf b (N r s) := hN
  have hT : FreeOf2 b Nᵀ := fun r s => h1 s r
  refine Matrix.ext fun i j => ?_
  have key : ∀ r s, d • (eU b r s * (N s r * M i j)) - eU b r s * (N i r * M s j) =
      d • (eU b r s * (M i j * N s r)) - eU b r s * (M i r * N s j) := fun r s => by
    have := congrArg (eU b r s * ·) (h s i r j)
    simp only [mul_sub, mul_smul_comm] at this
    exact this
  have hL : ((d0 (ins b Nᵀ) * (d • (1 : M2 (SlopeTestRemainingChoices S A)) - Q0 b) * M : M2 (SlopeTestRemainingChoices S A))) i j =
      d • (ins b Nᵀ * M i j) - ∑ k, ins b Nᵀ * (M k j * eU b i k) := by
    rw [mul_sub, sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.sub_apply,
      Matrix.smul_apply, d0, Matrix.diagonal_mul, Matrix.mul_apply]
    simp only [Matrix.diagonal_mul]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc]
    exact congrArg (ins b Nᵀ * ·) (hC k j i k).eq
  have hR : ((M * (d • (1 : M2 (SlopeTestRemainingChoices S A)) - Q0 b) * d0 (ins b Nᵀ) : M2 (SlopeTestRemainingChoices S A))) i j =
      d • (M i j * ins b Nᵀ) - ∑ k, eU b k j * M i k * ins b Nᵀ := by
    rw [mul_sub, sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.sub_apply,
      Matrix.smul_apply, d0, Matrix.mul_diagonal, Matrix.mul_diagonal, Matrix.mul_apply, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(hC i k k j).eq]
    rfl
  rw [hL, hR, ins_mul, mul_ins b _ _ (hM' i j),
    Finset.sum_congr rfl fun k _ => ins_mul_eU b i k (M k j) Nᵀ (hM' k j) hT,
    Finset.sum_congr rfl fun k _ => eU_mul_ins b k j (M i k) Nᵀ (hM' i k),
    Finset.sum_comm (f := fun k r => eU b r k * (Nᵀ r i * M k j)),
    Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => key r s

end

end Formalism.FourierDecayAlt.P.Wd3

namespace Formalism.FourierDecayAlt.P

open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd

theorem exchange_relation_plus : Formalism.FourierDecayAlt.Wd.ExchPlus := by
  unfold Formalism.FourierDecayAlt.Wd.ExchPlus
  intro K A S _ _ _ _ _ _ _ _ Ω RR TT q a Y Ya hmod hfree hY hYa
  obtain ⟨_, _, hrtt, _, _⟩ := hmod
  have hr : RTTat TT Ya Y := hrtt Ya hYa Y hY
  have hc := Wd3.plus_core a (TT Y) (TT Ya) (Y - Ya) (hfree Y) (hfree Ya)
    (Wd3.rtt_entry (TT Y) (TT Ya) (Y - Ya) hr)
  rw [Rh0, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, hc]

theorem exchange_relation_minus : Formalism.FourierDecayAlt.Wd.ExchMinus := by
  unfold Formalism.FourierDecayAlt.Wd.ExchMinus
  intro K A S _ _ _ _ _ _ _ _ Ω RR TT q b Y Yb hmod hfree hY hYb
  obtain ⟨_, _, hrtt, _, _⟩ := hmod
  have hr : RTTat TT Y Yb := hrtt Y hY Yb hYb
  have hc := Wd3.minus_core b (TT Y) (TT Yb) (Yb - Y) (hfree Y) (hfree Yb)
    (Wd3.rtt_entry (TT Yb) (TT Y) (Yb - Y) hr)
  simp only [Rht0, Matrix.mul_smul, Matrix.smul_mul, hc]

end Formalism.FourierDecayAlt.P
