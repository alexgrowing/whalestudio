import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.KroneckerMapOneRightNeZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.BlockDiagonalPreservesDegree
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockRaisingLowering.RaisingLoweringSplit
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockDegreeOne.OneDegOfHalves

noncomputable section

open Matrix FockH1Action MvPolynomial

namespace PI.FockOneDegW

section Ops

theorem omE_same {p q r s : ℕ} (a b : Ix p q) (c : Ix r s) (hab : sameBlock a b)
    (P : Pol p q r s) :
    omE ((a, c) : Ln p q r s) (b, c) P =
      ((if linePos ((a, c) : Ln p q r s) = true then
          X ((a, c) : Ln p q r s) * pderiv ((b, c) : Ln p q r s) P else 0)
        - (if linePos ((b, c) : Ln p q r s) = true then 0 else
          X ((b, c) : Ln p q r s) * pderiv ((a, c) : Ln p q r s) P))
      + (if a = b then
          (if linePos ((a, c) : Ln p q r s) = true then (1 / 2 : ℂ) else -(1 / 2)) • P else 0) := by
  classical

  have hl : linePos ((b, c) : Ln p q r s) = linePos ((a, c) : Ln p q r s) := by
    rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
      simp_all [sameBlock, linePos]
  have hab' : (((a, c) : Ln p q r s) = (b, c)) ↔ a = b := by simp
  rw [FockRL.omE_apply]
  unfold raiB lowB
  rw [hl]
  cases h : linePos ((a, c) : Ln p q r s)
  · by_cases hab2 : a = b
    · subst hab2
      simp [Derivation.leibniz, pderiv_X]
      module
    · have hne : ((a, c) : Ln p q r s) ≠ (b, c) := fun h' => hab2 (hab'.1 h')
      simp [hab2, hne, Derivation.leibniz, pderiv_X, Pi.single_apply, Ne.symm hne]
  · simp [hab']

theorem fockAct1_Eab_apply {p q r s : ℕ} (a b : Ix p q) (P : Pol p q r s) :
    fockAct1 p q r s (Eab a b) P = ∑ c : Ix r s, omE ((a, c) : Ln p q r s) (b, c) P := by
  classical
  rw [FockRL.fockAct1_eq, FockRL.omAct_eq_sum]
  simp [Eab, Matrix.single_apply, Matrix.one_apply, ite_and, Fintype.sum_prod_type,
    LinearMap.sum_apply]

theorem posOp_apply {p q r s : ℕ} (a b : Ix p q) (P : Pol p q r s) :
    posOp a b P = ∑ c : Ix r s, (if linePos ((a, c) : Ln p q r s) = true then
      X ((a, c) : Ln p q r s) * pderiv ((b, c) : Ln p q r s) P else 0) := by
  unfold posOp
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

theorem negOp_apply {p q r s : ℕ} (a b : Ix p q) (P : Pol p q r s) :
    negOp a b P = ∑ c : Ix r s, (if linePos ((a, c) : Ln p q r s) = true then 0 else
      X ((a, c) : Ln p q r s) * pderiv ((b, c) : Ln p q r s) P) := by
  unfold negOp
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs <;> simp

theorem sum_half {p q r s : ℕ} (a : Ix p q) :
    ∑ c : Ix r s, (if linePos ((a, c) : Ln p q r s) = true then (1 / 2 : ℂ) else -(1 / 2)) =
      (((kShift r s a : ℚ)) : ℂ) := by
  rcases a with a | a <;> simp [kShift, cPair, linePos, Fintype.sum_sum_type] <;> push_cast <;> ring

theorem fock_operators_kernel : OpsK := by
  intro p q r s a b hab
  apply LinearMap.ext
  intro P
  rw [fockAct1_Eab_apply]
  simp only [LinearMap.add_apply, LinearMap.sub_apply, posOp_apply, negOp_apply]
  rw [Finset.sum_congr rfl fun c _ => omE_same a b c hab P, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  congr 1
  split_ifs with h
  · subst h
    simp only [↓reduceIte, LinearMap.smul_apply, Module.End.one_apply]
    rw [← Finset.sum_smul, sum_half]
  · simp

end Ops

section Harm

theorem minus2_eq {p q r s : ℕ} (Z : Mat r s) (hZ : IsPC Z) (P : Pol p q r s) :
    minusPart (fockAct2 p q r s Z) P = -∑ c : Ix r s, ∑ d : Ix r s, Z c d • lowOp (p := p) (q := q) c d P := by
  classical

  have hside : ∀ (a : Ix p q) (c d : Ix r s), ¬ sameBlock c d →
      linePos ((a, d) : Ln p q r s) = true → linePos ((a, c) : Ln p q r s) = false := by
    intro a c d hcd hd
    rcases a with a | a <;> rcases c with c | c <;> rcases d with d | d <;>
      simp_all [sameBlock, linePos]
  have hOpp : FockRL.OppSign (Matrix.kroneckerMap (fun x y : ℂ => x * y) (1 : Mat p q) Z) := by
    rintro ⟨a, c⟩ ⟨b, d⟩ hne
    simp only [Matrix.kroneckerMap_apply, Matrix.one_apply] at hne
    split_ifs at hne with hab
    · subst hab
      have hcd : ¬ sameBlock c d := fun h => hne (by rw [hZ c d h, mul_zero])
      intro hEq
      rcases a with a | a <;> rcases c with c | c <;> rcases d with d | d <;>
        simp_all [sameBlock, linePos]
    · simp at hne
  rw [FockRL.fockAct2_eq, FockRL.omAct_eq_Rop_add_Lop _ hOpp,
    (FockRaiseLowGrade.raisingLoweringSplit _ _ _ (fun d P hP => FockRL.Rop_raise _ d P hP)
      (fun e P => FockRL.Lop_shift _ e P) P).2, FockRL.Lop_apply]

  have hL : ∀ (a : Ix p q) (c : Ix r s),
      (∑ l' : Ln p q r s, if linePos ((a, c) : Ln p q r s) = false ∧ linePos l' = true then
        Matrix.kroneckerMap (fun x y : ℂ => x * y) (1 : Mat p q) Z (a, c) l' •
          (-(pderiv ((a, c) : Ln p q r s) (pderiv l' P))) else 0) =
      ∑ d : Ix r s, if linePos ((a, d) : Ln p q r s) = true then
        Z c d • (-(pderiv ((a, c) : Ln p q r s) (pderiv ((a, d) : Ln p q r s) P))) else 0 := by
    intro a c
    rw [Fintype.sum_prod_type, Finset.sum_eq_single a]
    · refine Finset.sum_congr rfl fun d _ => ?_
      simp only [Matrix.kroneckerMap_apply, Matrix.one_apply_eq, one_mul]
      by_cases hZcd : Z c d = 0
      · simp [hZcd]
      · have hcd : ¬ sameBlock c d := fun h => hZcd (hZ c d h)
        by_cases hd : linePos ((a, d) : Ln p q r s) = true
        · simp [hd, hside a c d hcd hd]
        · simp [hd]
    · intro b _ hba
      refine Finset.sum_eq_zero fun d _ => ?_
      simp [Matrix.kroneckerMap_apply, Matrix.one_apply_ne (Ne.symm hba)]
    · simp
  have hR : -∑ c : Ix r s, ∑ d : Ix r s, Z c d • lowOp (p := p) (q := q) c d P =
      ∑ c : Ix r s, ∑ a : Ix p q, ∑ d : Ix r s, if linePos ((a, d) : Ln p q r s) = true then
        Z c d • (-(pderiv ((a, c) : Ln p q r s) (pderiv ((a, d) : Ln p q r s) P))) else 0 := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [lowOp, LinearMap.sum_apply, Finset.smul_sum, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun d _ => ?_
    split_ifs <;> simp
  rw [Fintype.sum_prod_type]
  simp only [hL]
  rw [Finset.sum_comm, hR]

theorem harmIff : HarmIff := by
  intro p q r s P
  unfold Harm2
  constructor
  · intro h c d hcd
    have hZ : IsPC (Matrix.single c d (1 : ℂ) : Mat r s) := by
      intro a b hab
      rw [Matrix.single_apply]
      split_ifs with h'
      · obtain ⟨rfl, rfl⟩ := h'
        exact absurd hab hcd
      · rfl
    have h1 := h _ hZ
    rw [minus2_eq _ hZ] at h1
    simpa [Matrix.single_apply, ite_and] using h1
  · intro h Z hZ
    rw [minus2_eq _ hZ, neg_eq_zero]
    refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
    by_cases hcd : sameBlock c d
    · rw [hZ c d hcd, zero_smul]
    · rw [h c d hcd, smul_zero]

end Harm

end PI.FockOneDegW
