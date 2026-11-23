import Formalism.SharpRestriction.CuspSpanNormBounds.DiagonalEntryIdentity
import Formalism.SharpRestriction.ParConsts

open Matrix MeasureTheory TensorProduct
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.ChoiceOfModulusAndDiscriminant

open Formalism.QuantumDeterminants Formalism.MainNotions.S.TopsChoicePartA

def adm1 (_D : Formalism.BasicNotions.D7) (CB : ℝ) : Prop := LemmaBCont CB

def adm2 (_D : Formalism.BasicNotions.D7) (CB : ℝ) : Prop := LemmaBAdj CB

def adm3 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stQ_cap

def ArchimedeanSignatureMatching (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stQ_anti

def adm5 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stQ_branch

def adm6 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stQ_wigner

def adm7 (_D : Formalism.BasicNotions.D7) (CB : ℝ) : Prop := LemmaBRad CB

def RadialGauge (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stA_gauge

def RadialPartHermitian (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stA_herm C

def RadialCapelli (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stA_capelli

def RadialHighestLevel (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.cuspSpanTopCondition

def RadialSigns (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stA_signs

def ConjugationNormInvariance (D : Formalism.BasicNotions.D7) (C : ℝ) : Prop :=
  RadialGauge D ∧ RadialPartHermitian D C ∧ RadialCapelli D ∧ RadialHighestLevel D ∧ RadialSigns D

def RadialRTTRelation (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stB_rtt

def RadialDeterminant (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stB_det

def ShaBoundTheoremB (D : Formalism.BasicNotions.D7) : Prop := RadialRTTRelation D ∧ RadialDeterminant D

def WordModuleHermitian (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stC_module C

def ModuleFormHermitian (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stC_rrherm C

def ModuleTelescoping (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stC_tele

def CornerEntryProduct (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stC_entry

def ModuleDualityInequality (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stC_dual C

def ModulePlaneWave (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.cuspSpanWaveCondition

def JetConsequence (D : Formalism.BasicNotions.D7) (C : ℝ) : Prop :=
  WordModuleHermitian D C ∧ ModuleFormHermitian D C ∧ ModuleTelescoping D ∧ CornerEntryProduct D ∧ ModuleDualityInequality D C ∧ ModulePlaneWave D

def ThetaAdjointPositiveScalar (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stD C

def ConclusionE (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stE C

def aux₃ (D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := ConjugationNormInvariance D C ∧ ShaBoundTheoremB D ∧ JetConsequence D C ∧ ThetaAdjointPositiveScalar D C ∧ ConclusionE D C

def admitted (D : Formalism.BasicNotions.D7) (CB : ℝ) : Prop :=
  adm1 D CB ∧ adm2 D CB ∧ adm3 D ∧ ArchimedeanSignatureMatching D ∧ adm5 D ∧ adm6 D ∧ adm7 D CB

def Stmt (D : Formalism.BasicNotions.D7) (CB C : ℝ) : Prop := admitted D CB → aux₃ D C

def UniformExportStatement : Prop := ∀ CB : ℝ, ∃ C₀ : ℝ, ∀ C ≥ C₀, ∀ D : Formalism.BasicNotions.D7, Stmt D CB C

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def admF1 (CB : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm1 (Fm.D x i) CB
def admF2 (CB : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm2 (Fm.D x i) CB
def admF3 : Prop := ∀ x (i : Fm.Ix x), adm3 (Fm.D x i)
def admF4 : Prop := ∀ x (i : Fm.Ix x), ArchimedeanSignatureMatching (Fm.D x i)
def admF5 : Prop := ∀ x (i : Fm.Ix x), adm5 (Fm.D x i)
def admF6 : Prop := ∀ x (i : Fm.Ix x), adm6 (Fm.D x i)
def admF7 (CB : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm7 (Fm.D x i) CB

def AdmF (CB : ℝ) : Prop :=
  admF1 Fm CB ∧ admF2 Fm CB ∧ admF3 Fm ∧ admF4 Fm ∧ admF5 Fm ∧ admF6 Fm ∧ admF7 Fm CB

def FamilyTargetsAtConstants (C : ℝ) : Prop := ∀ x (i : Fm.Ix x), aux₃ (Fm.D x i) C

def FamilyStatementAtConstants (CB C : ℝ) : Prop := AdmF Fm CB → FamilyTargetsAtConstants Fm C

end Family

theorem big_mono {C C' : ℝ} (h : C ≤ C') {L : Lev} {N : ℕ} {A : ℝ} {mm : ℕ} (hB : Big C' L N A mm) :
    Big C L N A mm := by
  unfold Big at *
  have hp : 0 ≤ ((L.r : ℝ) + 1) ^ 4 *
      ((N : ℝ) * ((2 * L.r + L.k0 + 2 : ℕ) : ℝ) ^ 2 + ((2 * L.r + L.k0 + 2 : ℕ) : ℝ) ^ 3) := by positivity
  have hle : C * ((L.r : ℝ) + 1) ^ 4 *
        ((N : ℝ) * ((2 * L.r + L.k0 + 2 : ℕ) : ℝ) ^ 2 + ((2 * L.r + L.k0 + 2 : ℕ) : ℝ) ^ 3) ≤
      C' * ((L.r : ℝ) + 1) ^ 4 *
        ((N : ℝ) * ((2 * L.r + L.k0 + 2 : ℕ) : ℝ) ^ 2 + ((2 * L.r + L.k0 + 2 : ℕ) : ℝ) ^ 3) := by
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right h hp
  exact ⟨hle.trans hB.1, hle.trans hB.2⟩

end Formalism.MainNotions.ChoiceOfModulusAndDiscriminant
