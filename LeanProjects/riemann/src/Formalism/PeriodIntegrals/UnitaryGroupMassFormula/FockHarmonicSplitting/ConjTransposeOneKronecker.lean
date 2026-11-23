import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FockHarmonicSplitting.FockInnerSelfReNonneg

noncomputable section

open MvPolynomial Matrix FockH1Action

namespace PI.FHS

section Sums

variable {σ : Type*}

lemma fockInner_sum_left {ι : Type*} (t : Finset ι) (f : ι → MvPolynomial σ ℂ)
    (Q : MvPolynomial σ ℂ) :
    fockInner (∑ i ∈ t, f i) Q = ∑ i ∈ t, fockInner (f i) Q := by
  classical
  refine Finset.induction_on t ?_ ?_
  · simp only [Finset.sum_empty, fockInner_zero_left]
  · intro i t hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, fockInner_add_left, ih]

lemma fockInner_sum_right {ι : Type*} (t : Finset ι) (f : ι → MvPolynomial σ ℂ)
    (P : MvPolynomial σ ℂ) :
    fockInner P (∑ i ∈ t, f i) = ∑ i ∈ t, fockInner P (f i) := by
  classical
  refine Finset.induction_on t ?_ ?_
  · simp only [Finset.sum_empty, fockInner_zero_right]
  · intro i t hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, fockInner_add_right, ih]

end Sums

variable {p q r s : ℕ}

lemma omE_apply_of_ne {l l' : Ln p q r s} (h : l ≠ l') (P : Pol p q r s) :
    omE l l' P = raiB l (lowB l' P) := by
  rw [FockH1Action.omE, if_neg h, add_zero]; rfl

private theorem raiB_apply_eq_X_mul_of_linePos {m : FockH1Action.Ln p q r s} (h : FockH1Action.linePos m = true)
    (P : FockH1Action.Pol p q r s) : FockH1Action.raiB m P = X m * P := by
  rw [FockH1Action.raiB, if_pos h]; rfl

private theorem raiB_apply_eq_neg_pderiv_of_not_linePos {m : FockH1Action.Ln p q r s} (h : FockH1Action.linePos m = false)
    (P : FockH1Action.Pol p q r s) : FockH1Action.raiB m P = -(pderiv m P) := by
  rw [FockH1Action.raiB, if_neg (by simp [h])]; rfl

private theorem lowB_apply_eq_pderiv_of_linePos {m : FockH1Action.Ln p q r s} (h : FockH1Action.linePos m = true)
    (P : FockH1Action.Pol p q r s) : FockH1Action.lowB m P = pderiv m P := by
  rw [FockH1Action.lowB, if_pos h]; rfl

private theorem lowB_apply_eq_X_mul_of_not_linePos {m : FockH1Action.Ln p q r s} (h : FockH1Action.linePos m = false)
    (P : FockH1Action.Pol p q r s) : FockH1Action.lowB m P = X m * P := by
  rw [FockH1Action.lowB, if_neg (by simp [h])]; rfl

lemma omE_adj {l l' : Ln p q r s} (h : linePos l ≠ linePos l') (P Q : Pol p q r s) :
    fockInner (omE l l' P) Q = - fockInner P (omE l' l Q) := by
  have hne : l ≠ l' := fun e => h (e ▸ rfl)
  rw [omE_apply_of_ne hne, omE_apply_of_ne (Ne.symm hne)]
  cases hl : FockH1Action.linePos l <;> cases hl' : FockH1Action.linePos l'
  · exact absurd (hl.trans hl'.symm) h
  · rw [lowB_apply_eq_pderiv_of_linePos hl', raiB_apply_eq_neg_pderiv_of_not_linePos hl, lowB_apply_eq_X_mul_of_not_linePos hl, raiB_apply_eq_X_mul_of_linePos hl',
      fockInner_neg_left, fockInner_pderiv, fockInner_pderiv]
  · rw [lowB_apply_eq_X_mul_of_not_linePos hl', raiB_apply_eq_X_mul_of_linePos hl, lowB_apply_eq_pderiv_of_linePos hl, raiB_apply_eq_neg_pderiv_of_not_linePos hl',
      fockInner_neg_right, neg_neg, fockInner_X_mul, fockInner_X_mul]
  · exact absurd (hl.trans hl'.symm) h

lemma omAct_apply (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) (P : Pol p q r s) :
    omAct p q r s M P = ∑ l, ∑ l', M l l' • omE l l' P := by
  simp [FockH1Action.omAct, LinearMap.sum_apply, LinearMap.smulRight_apply]

def Mixed (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) : Prop :=
  ∀ l l', M l l' ≠ 0 → linePos l ≠ linePos l'

lemma omAct_adj (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) (hM : Mixed M) (P Q : Pol p q r s) :
    fockInner (omAct p q r s M P) Q = - fockInner P (omAct p q r s Mᴴ Q) := by
  rw [omAct_apply, omAct_apply]
  simp only [fockInner_sum_left, fockInner_sum_right, fockInner_smul_left,
    fockInner_smul_right, Matrix.conjTranspose_apply]
  conv_rhs => rw [Finset.sum_comm]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l' _ => ?_
  by_cases hz : M l l' = 0
  · simp [hz]
  · rw [omE_adj (hM l l' hz), mul_neg]
    rfl

lemma sameBlock_symm {a b : Ix p q} (h : sameBlock a b) : sameBlock b a := by
  cases a <;> cases b <;> simp_all [FockH1Action.sameBlock]

lemma isPC_ct {Z : Mat p q} (h : IsPC Z) : IsPC Zᴴ := by
  intro a b hab
  simp [Matrix.conjTranspose_apply, h b a (sameBlock_symm hab)]

lemma fockAct1_eq (Z : Mat p q) :
    fockAct1 p q r s Z = omAct p q r s (Matrix.kroneckerMap (fun a b => a * b) Z (1 : Mat r s)) :=
  rfl

lemma fockAct2_eq (Z : Mat r s) :
    fockAct2 p q r s Z = omAct p q r s (Matrix.kroneckerMap (fun a b => a * b) (1 : Mat p q) Z) :=
  rfl

lemma mixed1 {Z : Mat p q} (hZ : IsPC Z) :
    Mixed (Matrix.kroneckerMap (fun a b => a * b) Z (1 : Mat r s)) := by
  rintro ⟨a, c⟩ ⟨b, d⟩ hne
  simp only [Matrix.kroneckerMap_apply] at hne
  by_cases hcd : c = d
  · subst hcd
    have hs : ¬ FockH1Action.sameBlock a b := fun hab => hne (by rw [hZ a b hab, zero_mul])
    clear hne hZ
    rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
      simp_all [FockH1Action.sameBlock, FockH1Action.linePos]
  · exact absurd (by rw [Matrix.one_apply_ne hcd, mul_zero]) hne

lemma mixed2 {Z : Mat r s} (hZ : IsPC Z) :
    Mixed (Matrix.kroneckerMap (fun a b => a * b) (1 : Mat p q) Z) := by
  rintro ⟨a, c⟩ ⟨b, d⟩ hne
  simp only [Matrix.kroneckerMap_apply] at hne
  by_cases hab : a = b
  · subst hab
    have hs : ¬ FockH1Action.sameBlock c d := fun hcd => hne (by rw [hZ c d hcd, mul_zero])
    clear hne hZ
    rcases a with a | a <;> rcases c with c | c <;> rcases d with d | d <;>
      simp_all [FockH1Action.sameBlock, FockH1Action.linePos]
  · exact absurd (by rw [Matrix.one_apply_ne hab, zero_mul]) hne

lemma conjTranspose_kronecker_one (Z : Mat p q) :
    (Matrix.kroneckerMap (fun a b => a * b) Z (1 : Mat r s))ᴴ =
      Matrix.kroneckerMap (fun a b => a * b) Zᴴ (1 : Mat r s) := by
  ext ⟨a, c⟩ ⟨b, d⟩
  simp only [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply]
  by_cases hcd : c = d
  · subst hcd; simp
  · rw [Matrix.one_apply_ne hcd, Matrix.one_apply_ne (Ne.symm hcd)]; simp

lemma conjTranspose_one_kronecker (Z : Mat r s) :
    (Matrix.kroneckerMap (fun a b => a * b) (1 : Mat p q) Z)ᴴ =
      Matrix.kroneckerMap (fun a b => a * b) (1 : Mat p q) Zᴴ := by
  ext ⟨a, c⟩ ⟨b, d⟩
  simp only [Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply]
  by_cases hab : a = b
  · subst hab; simp
  · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne (Ne.symm hab)]; simp

theorem fockAct1_adj {Z : Mat p q} (hZ : IsPC Z) (P Q : Pol p q r s) :
    fockInner (fockAct1 p q r s Z P) Q = - fockInner P (fockAct1 p q r s Zᴴ Q) := by
  rw [fockAct1_eq, fockAct1_eq,
    omAct_adj _ (mixed1 hZ), conjTranspose_kronecker_one]

theorem fockAct2_adj {Z : Mat r s} (hZ : IsPC Z) (P Q : Pol p q r s) :
    fockInner (fockAct2 p q r s Z P) Q = - fockInner P (fockAct2 p q r s Zᴴ Q) := by
  rw [fockAct2_eq, fockAct2_eq,
    omAct_adj _ (mixed2 hZ), conjTranspose_one_kronecker]

end PI.FHS
