import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountOfIntegral

noncomputable section

namespace Formalism.L2.SG.Pf.PCount

open Formalism.MainNotions.S Formalism.L2.SG.Pf.AtPt

def BridgeIso : Prop :=
  ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Loc.Model F E) (m : ℕ) (n s : E) (P₁ P₂ X₁ X₂ L₁ U₁ L₂ U₂ : Matrix (Fin (m + 1)) (Fin (m + 1)) E),
    IsLo L₁ → IsUp U₁ → IsLo L₂ → IsUp U₂ → P₁ = L₁ * X₁ * U₁ → P₂ = L₂ * X₂ * U₂ →
    (∀ a : Fin m, X₁ a.castSucc (Fin.last m) = 0 ∧ X₁ (Fin.last m) a.castSucc = 0 ∧
      X₂ a.castSucc (Fin.last m) = 0 ∧ X₂ (Fin.last m) a.castSucc = 0) →
    X₁ (Fin.last m) (Fin.last m) = s → X₂ (Fin.last m) (Fin.last m) = s → IsUnit (s + n) → n ∈ M.R →
    ∀ (Y₁ Y₂ : M.Mat m) (be₁ be₂ al₁ al₂ : Fin m → M.R),
      (∀ a b : Fin m, (Y₁.Z a b : E) = P₁ a.castSucc b.castSucc ∧ (Y₂.Z a b : E) = P₂ a.castSucc b.castSucc) →
      (∀ a : Fin m, (be₁ a : E) = P₁ a.castSucc (Fin.last m) ∧ (be₂ a : E) = P₂ a.castSucc (Fin.last m) ∧
        (al₁ a : E) = P₁ (Fin.last m) a.castSucc ∧ (al₂ a : E) = P₂ (Fin.last m) a.castSucc) →
      (∀ a b, P₁ a b ∈ M.R) → (∀ a b, P₂ a b ∈ M.R) →
      ∀ Z₁ Z₂ : M.Mat (m + 1), Z₁.Z.map M.R.subtype = P₁ + n • Ecorner m →
        Z₂.Z.map M.R.subtype = P₂ + n • Ecorner m → M.nIsoBA Y₁ Y₂ be₁ be₂ al₁ al₂ = M.nIso Z₁ Z₂

section Det

variable {K : Type*} [CommRing K] {m : ℕ}

theorem det_shift {n s : K} {P X L U : Matrix (Fin (m + 1)) (Fin (m + 1)) K} (hL : IsLo L) (hU : IsUp U)
    (hP : P = L * X * U) (hX : ∀ a : Fin m, X a.castSucc (Fin.last m) = 0 ∧ X (Fin.last m) a.castSucc = 0)
    (hs : X (Fin.last m) (Fin.last m) = s) : (P + n • Ecorner m).det = (s + n) * leadM P m := by
  have e : P + n • Ecorner m = L * (X + n • Ecorner m) * U := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, lo_corner_up hL hU, hP]
  have hX' : ∀ a : Fin m, (X + n • Ecorner m : Matrix (Fin (m + 1)) (Fin (m + 1)) K) a.castSucc (Fin.last m) = 0 ∧
      (X + n • Ecorner m : Matrix (Fin (m + 1)) (Fin (m + 1)) K) (Fin.last m) a.castSucc = 0 := fun a => by
    simp [Ecorner, (hX a).1, (hX a).2, Fin.castSucc_ne_last]
  rw [e, Matrix.det_mul, Matrix.det_mul, det_lo' hL, det_up' hU, one_mul, mul_one, det_of_corner _ hX',
    leadM_add_corner, hP, leadM_mul hL hU]
  simp [Ecorner, hs]

end Det

section Model

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem lead_eq_head (M : Loc.Model F E) {m : ℕ} (P : Matrix (Fin (m + 1)) (Fin (m + 1)) E) (Y : M.Mat m)
    (hY : ∀ a b : Fin m, (Y.Z a b : E) = P a.castSucc b.castSucc) : leadM P m = (Y.Z.map M.R.subtype).det := by
  unfold leadM
  rw [dif_pos (Nat.le_succ m)]
  congr 1
  ext a b
  exact (hY a b).symm

end Model

theorem bridgeBA_of (hI : BridgeIso) : BridgeBA := by
  intro F _ _ _ E _ _ _ _ M m n s P₁ P₂ X₁ X₂ L₁ U₁ L₂ U₂ hL₁ hU₁ hL₂ hU₂ hP₁ hP₂ hX h₁ h₂ hsn hn Y₁ Y₂
    be₁ be₂ al₁ al₂ hY hba hi₁ hi₂
  have hX₁ : ∀ a : Fin m, X₁ a.castSucc (Fin.last m) = 0 ∧ X₁ (Fin.last m) a.castSucc = 0 :=
    fun a => ⟨(hX a).1, (hX a).2.1⟩
  have hX₂ : ∀ a : Fin m, X₂ a.castSucc (Fin.last m) = 0 ∧ X₂ (Fin.last m) a.castSucc = 0 :=
    fun a => ⟨(hX a).2.2.1, (hX a).2.2.2⟩
  have hu₁ : IsUnit (P₁ + n • Ecorner m).det := by
    rw [det_shift hL₁ hU₁ hP₁ hX₁ h₁, lead_eq_head M P₁ Y₁ fun a b => (hY a b).1]
    exact hsn.mul Y₁.unit
  have hu₂ : IsUnit (P₂ + n • Ecorner m).det := by
    rw [det_shift hL₂ hU₂ hP₂ hX₂ h₂, lead_eq_head M P₂ Y₂ fun a b => (hY a b).2]
    exact hsn.mul Y₂.unit
  have hint : ∀ {P : Matrix (Fin (m + 1)) (Fin (m + 1)) E}, (∀ a b, P a b ∈ M.R) →
      ∀ a b, (P + n • Ecorner m : Matrix (Fin (m + 1)) (Fin (m + 1)) E) a b ∈ M.R := fun hP a b => by
    simp only [Matrix.add_apply, Matrix.smul_apply, Ecorner, Matrix.of_apply, smul_eq_mul]
    split_ifs
    · exact M.R.add_mem (hP a b) (by rw [mul_one]; exact hn)
    · rw [mul_zero, add_zero]; exact hP a b
  refine ⟨mkMat M _ (hint hi₁) hu₁, mkMat M _ (hint hi₂) hu₂, rfl, rfl, ?_⟩
  exact hI M m n s P₁ P₂ X₁ X₂ L₁ U₁ L₂ U₂ hL₁ hU₁ hL₂ hU₂ hP₁ hP₂ hX h₁ h₂ hsn hn Y₁ Y₂ be₁ be₂ al₁ al₂ hY hba
    hi₁ hi₂ _ _ rfl rfl

theorem partnerCount_of_iso {D : Formalism.BasicNotions.D7} (Zd : Formalism.L2.SG.TermLoc.LocDat D) (hT2 : Formalism.MainNotions.ThinScalesBound.T2 D)
    (hI : IntGenP Zd) (hB : BridgeIso) : PartnerIsomorphismCount Zd :=
  partnerCount_of_integral Zd hT2 hI (bridgeBA_of hB)

end Formalism.L2.SG.Pf.PCount
