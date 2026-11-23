import Formalism.SharpRestriction.CuspSpanNormBounds.DiagonalEntryIdentity
import Formalism.SharpRestriction.ParConsts

open Matrix MeasureTheory TensorProduct
open scoped ContDiff

noncomputable section

namespace Formalism.MainNotions.RadialRules

open Formalism.QuantumDeterminants Formalism.MainNotions.S.TopsChoicePartA Formalism.MainNotions.S.LevR

export Formalism.MainNotions.S.UnitaryLevelOperators (lenI AEq mid3 wnormSq)

def adm1 (_D : Formalism.BasicNotions.D7) (CB : ℝ) : Prop := LemmaBCont CB

def adm2 (_D : Formalism.BasicNotions.D7) (CB : ℝ) : Prop := LemmaBAdj CB

def adm3 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stQ_cap

def ArchimedeanSignatureMatching (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stQ_anti

def adm5 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stQ_branch

def adm6 (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stQ_wigner

def adm10 (_D : Formalism.BasicNotions.D7) (CB : ℝ) : Prop := LemmaBRad CB

def RulesGauge (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stA_gauge

def ResidueBoundAlt (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stA_herm C

def RulesCapelli (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stA_capelli

def RadialRulesCombined (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.cuspSpanTopCondition

def RulesSigns (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stA_signs

def adm7 (D : Formalism.BasicNotions.D7) (C : ℝ) : Prop :=
  RulesGauge D ∧ ResidueBoundAlt D C ∧ RulesCapelli D ∧ RadialRulesCombined D ∧ RulesSigns D

def RulesRTT (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stB_rtt

def RulesDeterminant (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stB_det

def adm8 (D : Formalism.BasicNotions.D7) : Prop := RulesRTT D ∧ RulesDeterminant D

def RulesWordModule (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stC_module C

def RulesFormHermitian (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stC_rrherm C

def RulesTelescoping (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stC_tele

def RadialRuleLeadingEntry (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.stC_entry

def RulesDuality (_D : Formalism.BasicNotions.D7) (C : ℝ) : Prop := S.UnitaryLevelOperators.stC_dual C

def RulesPlaneWave (_D : Formalism.BasicNotions.D7) : Prop := S.UnitaryLevelOperators.cuspSpanWaveCondition

def adm9 (D : Formalism.BasicNotions.D7) (C : ℝ) : Prop :=
  RulesWordModule D C ∧ RulesFormHermitian D C ∧ RulesTelescoping D ∧ RadialRuleLeadingEntry D ∧ RulesDuality D C ∧ RulesPlaneWave D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

section Parts

variable {B : Base E} {r : ℕ} (C : Ctx B r) (Γ : GCtx E r)

def LevelRDecomposition (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) : Prop :=
  S.UnitaryLevelOperators.stLevR C h SS

def GroupLevelInvariants (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) : Prop :=
  S.UnitaryLevelOperators.stLev0 C Γ h SS

def LevelOperatorRules (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) : Prop :=
  S.UnitaryLevelOperators.stRules C h SS

def ProductRuleLevelR (Cv : ℝ) (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) :
    Prop := S.UnitaryLevelOperators.stProd C Cv h SS

def FrameFactorisationLevelR (okF : ℕ → Prop) (h : (Fin (r + 1) → ℂ) → E →L[ℂ] E) (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) :
    Prop := S.UnitaryLevelOperators.stFrameR C okF h SS

def FrameComponentsGroup (Cr : Ctx B 0) (C0 : Ctx B r) (lift : Op 1 E → Op (r + 1) E)
    (pull : ((Fin 1 → ℂ) → E →L[ℂ] E) → (Fin (r + 1) → ℂ) → E →L[ℂ] E)
    (h : (Fin 1 → ℂ) → E →L[ℂ] E) (SS : Fin B.k0 → (Fin 1 → ℂ) → E →L[ℂ] E) : Prop :=
  S.UnitaryLevelOperators.stFrameG Cr C0 lift pull h SS

def AuxBlock3 (C1 C2 : ℝ) (SS : Fin B.k0 → (Fin (r + 1) → ℂ) → E →L[ℂ] E) : Prop := S.UnitaryLevelOperators.stRes C C1 C2 SS

end Parts

def OmegaPolynomialVanishes (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Prop := S.UnitaryLevelOperators.stOm k r z z'

def aux₃ (_D : Formalism.BasicNotions.D7) (C Cv C1 C2 : ℝ) : Prop := S.UnitaryLevelOperators.stLevel C Cv C1 C2

def admitted (D : Formalism.BasicNotions.D7) (CB Ca : ℝ) : Prop :=
  adm1 D CB ∧ adm2 D CB ∧ adm3 D ∧ ArchimedeanSignatureMatching D ∧ adm5 D ∧ adm6 D ∧ adm7 D Ca ∧ adm8 D ∧ adm9 D Ca ∧ adm10 D CB

def Stmt (D : Formalism.BasicNotions.D7) (CB Ca C Cv C1 C2 : ℝ) : Prop := admitted D CB Ca → aux₃ D C Cv C1 C2

def UniformExportStatement : Prop :=
  ∀ CB Ca : ℝ, ∃ C₀ Cv : ℝ, ∀ C1 : ℝ, ∃ C2 : ℝ, ∀ C ≥ C₀, ∀ D : Formalism.BasicNotions.D7, Stmt D CB Ca C Cv C1 C2

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def admF1 (CB : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm1 (Fm.D x i) CB
def admF2 (CB : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm2 (Fm.D x i) CB
def admF3 : Prop := ∀ x (i : Fm.Ix x), adm3 (Fm.D x i)
def admF4 : Prop := ∀ x (i : Fm.Ix x), ArchimedeanSignatureMatching (Fm.D x i)
def admF5 : Prop := ∀ x (i : Fm.Ix x), adm5 (Fm.D x i)
def admF6 : Prop := ∀ x (i : Fm.Ix x), adm6 (Fm.D x i)
def admF7 (Ca : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm7 (Fm.D x i) Ca
def admF8 : Prop := ∀ x (i : Fm.Ix x), adm8 (Fm.D x i)
def admF9 (Ca : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm9 (Fm.D x i) Ca
def FamilyRowsCountHypothesis (CB : ℝ) : Prop := ∀ x (i : Fm.Ix x), adm10 (Fm.D x i) CB

def AdmF (CB Ca : ℝ) : Prop :=
  admF1 Fm CB ∧ admF2 Fm CB ∧ admF3 Fm ∧ admF4 Fm ∧ admF5 Fm ∧ admF6 Fm ∧ admF7 Fm Ca ∧ admF8 Fm ∧ admF9 Fm Ca ∧
    FamilyRowsCountHypothesis Fm CB

def FamilyTargetsAtConstants (C Cv C1 C2 : ℝ) : Prop := ∀ x (i : Fm.Ix x), aux₃ (Fm.D x i) C Cv C1 C2

def OrbitValuationBound (C C1 : ℝ) : Prop := ∃ Cv C2 : ℝ, FamilyTargetsAtConstants Fm C Cv C1 C2

def FamilyStatementAtConstants (CB Ca C Cv C1 C2 : ℝ) : Prop := AdmF Fm CB Ca → FamilyTargetsAtConstants Fm C Cv C1 C2

def KudlaFamilyStatement (CB Ca C C1 : ℝ) : Prop := AdmF Fm CB Ca → OrbitValuationBound Fm C C1

end Family

theorem lemma_B_three_iff (D : Formalism.BasicNotions.D7) (CB : ℝ) : (adm1 D CB ∧ adm2 D CB ∧ adm10 D CB) ↔ LemmaBThreeClauses CB := Iff.rfl

theorem radial_statement_indep_datum (D D' : Formalism.BasicNotions.D7) (C Cv C1 C2 : ℝ) : aux₃ D C Cv C1 C2 ↔ aux₃ D' C Cv C1 C2 := Iff.rfl

theorem Adm_indep (D D' : Formalism.BasicNotions.D7) (CB Ca : ℝ) : admitted D CB Ca ↔ admitted D' CB Ca := Iff.rfl

theorem rules_family_of_uniform (H : UniformExportStatement) (CB Ca : ℝ) : ∃ C₀ : ℝ, ∀ C ≥ C₀, ∀ C1 : ℝ, ∀ {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps),
    KudlaFamilyStatement Fm CB Ca C C1 := by
  obtain ⟨C₀, Cv, H⟩ := H CB Ca
  refine ⟨C₀, fun C hC C1 eps Fm hA => ?_⟩
  obtain ⟨C2, H⟩ := H C1
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ := hA
  exact ⟨Cv, C2, fun x i => H C hC (Fm.D x i)
    ⟨a1 x i, a2 x i, a3 x i, a4 x i, a5 x i, a6 x i, a7 x i, a8 x i, a9 x i, a10 x i⟩⟩

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

theorem theorem_c_mono_constant (D : Formalism.BasicNotions.D7) {C C' : ℝ} (Cv C1 C2 : ℝ) (hc : C ≤ C') (H : aux₃ D C Cv C1 C2) :
    aux₃ D C' Cv C1 C2 := by
  intro Lt u u' I hr hy hy' R hR
  obtain ⟨h, SS, p1, p2, p3, p4, p5, p6, p7, p8⟩ := H Lt u u' I hr hy hy' R hR
  refine ⟨h, SS, fun hh A mm hO hB => p1 hh A mm hO (big_mono hc hB), p2, p3, p4, ?_, p6, p7, p8⟩
  intro hh A mm hO w hw
  obtain ⟨f1, f2⟩ := p5 hh A mm hO w hw
  exact ⟨fun hB => f1 (big_mono hc hB), f2⟩

end Formalism.MainNotions.RadialRules
