import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Lemma44IdentityOfRawTail
import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.LiftSubstitutionCoeffDivisible

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt

section Order

variable {O : Type} [CommRing O] [IsDomain O] {σ : Type}

theorem inWj_mul {w : O} {P Q : MvPolynomial σ (KK O)} {a b : ℕ} (hP : InWj w P a) (hQ : InWj w Q b) :
    InWj w (P * Q) (a + b) := by
  classical
  intro m
  choose cp hcp using hP
  choose cq hcq using hQ
  refine ⟨∑ x ∈ Finset.HasAntidiagonal.antidiagonal m, cp x.1 * cq x.2, ?_⟩
  rw [coeff_mul, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hcp, hcq, ← map_mul]
  congr 1
  ring

theorem inWj_one (w : O) : InWj w (1 : MvPolynomial σ (KK O)) 0 := by
  classical
  intro m
  rw [coeff_one]
  split_ifs
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp⟩

theorem inWj_pow {w : O} {P : MvPolynomial σ (KK O)} {a : ℕ} (hP : InWj w P a) (n : ℕ) : InWj w (P ^ n) (n * a) := by
  induction n with
  | zero => simpa using inWj_one w
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact inWj_mul ih hP

theorem inWj_prod {w : O} {ι : Type} (s : Finset ι) (P : ι → MvPolynomial σ (KK O)) (a : ι → ℕ)
    (h : ∀ i ∈ s, InWj w (P i) (a i)) : InWj w (∏ i ∈ s, P i) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using inWj_one w
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact inWj_mul (h i (Finset.mem_insert_self _ _)) (ih fun l hl => h l (Finset.mem_insert_of_mem hl))

end Order

section Rg

variable {p f : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra (WF p f) O]
  {k : ℕ} {ι : Type}

theorem inWjRg_mul {w : O} {r : ℕ} {LL : LiftLetters ι} {g : Matrix (Fin k) (Fin k) (WF p f)}
    {F G : MvPolynomial (ι × Fin k) (KK O)} {a b : ℕ} (hF : InWjRg p f O w r LL g F a)
    (hG : InWjRg p f O w r LL g G b) : InWjRg p f O w r LL g (F * G) (a + b) := by
  unfold InWjRg at *
  rw [map_mul]
  exact inWj_mul hF hG

theorem inWjRg_pow {w : O} {r : ℕ} {LL : LiftLetters ι} {g : Matrix (Fin k) (Fin k) (WF p f)}
    {F : MvPolynomial (ι × Fin k) (KK O)} {a : ℕ} (hF : InWjRg p f O w r LL g F a) (n : ℕ) :
    InWjRg p f O w r LL g (F ^ n) (n * a) := by
  unfold InWjRg at *
  rw [map_pow]
  exact inWj_pow hF n

theorem inWjRg_prod {w : O} {r : ℕ} {LL : LiftLetters ι} {g : Matrix (Fin k) (Fin k) (WF p f)} {κ : Type}
    (s : Finset κ) (F : κ → MvPolynomial (ι × Fin k) (KK O)) (a : κ → ℕ)
    (h : ∀ i ∈ s, InWjRg p f O w r LL g (F i) (a i)) : InWjRg p f O w r LL g (∏ i ∈ s, F i) (∑ i ∈ s, a i) := by
  unfold InWjRg at *
  rw [map_prod]
  exact inWj_prod s _ a h

def hKey (O : Type) [CommRing O] [IsDomain O] {ι : Type} (k : ℕ) (l l' : ι) : MvPolynomial (ι × Fin k) (KK O) :=
  ∑ a : Fin k, X (l, a) * X (l', a)

theorem hook_key_lift_exact (w : O) (LL : LiftLetters ι) (r : ℕ) (g : Matrix (Fin k) (Fin k) (WF p f)) (hg : IsGLW g) (l l' : ι)
    (hl : LL.vec l = true) (hl' : LL.vec l' = false) (hpos : LL.pos l = LL.pos l') :
    liftSubst p f O w r LL g (hKey O k l l') = C (algebraMap O (KK O) w) * hKey O k l l' := by
  classical
  unfold hKey
  rw [map_sum]
  simp only [map_mul, liftSubst_X_vec p f O w LL r g hg l _ hl, liftSubst_X_cov p f O w LL r g l' _ hl']
  have hinv : ∀ b b' : Fin k, ∑ a : Fin k, sigMat p f O g⁻¹ (LL.pos l) b a * sigMat p f O g (LL.pos l') a b' =
      if b = b' then 1 else 0 := by
    intro b b'
    rw [← hpos, ← Matrix.mul_apply, ← sigMat_mul, Matrix.nonsing_inv_mul g hg, sigMat_one, Matrix.one_apply]
  have hd : ∀ b : Fin k, dW O w LL r l b * dW O w LL r l' b = w := by
    intro b
    by_cases hb : b.val < r
    · have hb' : ¬ r ≤ b.val := by omega
      simp [dW, hl, hl', hb, hb']
    · have hb' : r ≤ b.val := by omega
      simp [dW, hl, hl', hb, hb']
  calc ∑ a : Fin k, (∑ b : Fin k, C (algebraMap O (KK O) (dW O w LL r l b)) * X (l, b) *
          C (sigMat p f O g⁻¹ (LL.pos l) b a)) *
        (∑ b' : Fin k, C (algebraMap O (KK O) (dW O w LL r l' b')) * X (l', b') * C (sigMat p f O g (LL.pos l') a b'))
      = ∑ b : Fin k, ∑ b' : Fin k, C (algebraMap O (KK O) (dW O w LL r l b)) * X (l, b) *
          (C (algebraMap O (KK O) (dW O w LL r l' b')) * X (l', b')) *
          C (∑ a : Fin k, sigMat p f O g⁻¹ (LL.pos l) b a * sigMat p f O g (LL.pos l') a b') := by
        simp only [Finset.sum_mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b' _ => ?_
        rw [map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [map_mul]
        ring
    _ = ∑ b : Fin k, C (algebraMap O (KK O) (dW O w LL r l b)) * X (l, b) *
          (C (algebraMap O (KK O) (dW O w LL r l' b)) * X (l', b)) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        simp only [hinv]
        rw [Finset.sum_eq_single b]
        · simp
        · intro b' _ hne
          rw [if_neg (Ne.symm hne)]
          simp
        · intro h; exact absurd (Finset.mem_univ b) h
    _ = C (algebraMap O (KK O) w) * ∑ a : Fin k, X (l, a) * X (l', a) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        have hC : (C (algebraMap O (KK O) w) : MvPolynomial (ι × Fin k) (KK O)) =
            C (algebraMap O (KK O) (dW O w LL r l b)) * C (algebraMap O (KK O) (dW O w LL r l' b)) := by
          rw [← map_mul, ← map_mul, hd b]
        rw [hC]
        ring

theorem hook_key_order_ge_one (w : O) (LL : LiftLetters ι) (r : ℕ) (g : Matrix (Fin k) (Fin k) (WF p f)) (hg : IsGLW g) (l l' : ι)
    (hl : LL.vec l = true) (hl' : LL.vec l' = false) (hpos : LL.pos l = LL.pos l') :
    InWjRg p f O w r LL g (hKey O k l l') 1 := by
  classical
  unfold InWjRg
  rw [hook_key_lift_exact w LL r g hg l l' hl hl' hpos, C_mul_eq_smul]
  have h0 : InWj w (hKey O k l l') 0 := by
    unfold hKey
    refine (wjSub w 0).sum_mem fun a _ => ?_
    have hX : ∀ v : ι × Fin k, InWj w (X v : MvPolynomial (ι × Fin k) (KK O)) 0 := by
      intro v m
      rw [coeff_X]
      split_ifs
      · exact ⟨1, by simp⟩
      · exact ⟨0, by simp⟩
    exact inWj_mul (hX _) (hX _)
  have := wj_smul_pow h0 1
  rwa [pow_one, zero_add] at this

end Rg

end Formalism.MainNotions.ColumnSystems.Pf
