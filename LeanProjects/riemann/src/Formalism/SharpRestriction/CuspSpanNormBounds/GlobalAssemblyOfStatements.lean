import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds

noncomputable section

namespace Formalism.MainNotions.VanishingOnXAndXPlusGlobal

export Formalism.MainNotions.S.UnitaryVolumeMass (DefiniteComplementRank Lem1 Lem2 LatticeSpanEquality ThmA HyperplaneEquality ThmB)

open NumberField Formalism.BasicNotions Formalism.MainNotions.S.Lat Module

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev Lt (D : D7) : Type := Submodule (𝓞 D.host.E) (hS D).V

abbrev Fl (D : D7) (T : ℕ) : Type := LFlag (hS D) D.R.rS ((T : ℕ) : D.host.E)

def adm1 (D : D7) : Prop :=
  S.UnitaryVolumeMass.stGlue D

def adm2 : Prop :=
  S.UnitaryVolumeMass.stBRhad

def adm3 (D : D7) : Prop :=
  S.UnitaryVolumeMass.stKron D

def Conclusion0 (D : D7) : Prop :=
  S.UnitaryVolumeMass.DefiniteComplementAllWords D

def Conclusion1 (D : D7) : Prop :=
  S.UnitaryVolumeMass.stLem1 D

def Conclusion2 (D : D7) : Prop :=
  S.UnitaryVolumeMass.stLem2 D

def PointsLemma (D : D7) : Prop :=
  S.UnitaryVolumeMass.HyperplaneRankAllWords D

def Conclusion4 (D : D7) : Prop :=
  S.UnitaryVolumeMass.stThmA D

def RelativePresentationLiterature (D : D7) : Prop :=
  S.UnitaryVolumeMass.DefiniteRankOneAllWords D

def PairsWithFiniteGroup (D : D7) : Prop :=
  S.UnitaryVolumeMass.stThmB D

def Conclusion5 (D : D7) : Prop := RelativePresentationLiterature D ∧ PairsWithFiniteGroup D

def TwistTheoremAtIndex (D : D7) : Prop :=
  ∀ (u : D.what₂.Word) (T' : ℕ) (Λ : Lt D) (F : Fl D (Tu D u)) (F' : Fl D T'),
    FixedHyp D Λ F → PrimeHyp D u T' → IsTerm Λ (gS D) F F' →
      ∀ τ : D.host.E →+* ℂ, 0 < (τ (Gval F F')).re ∧ (τ (Gval F F')).im = 0

def admitted (D : D7) : Prop := adm1 D ∧ adm2 ∧ adm3 D

def Conclusion₂ (D : D7) : Prop := Conclusion0 D ∧ Conclusion1 D ∧ Conclusion2 D ∧ PointsLemma D ∧ Conclusion4 D ∧ Conclusion5 D

def Stmt (D : D7) : Prop := admitted D → Conclusion₂ D

def HarishChandraFormulaStatement (D : D7) : Prop := Conclusion0 D

def IntegralityFromMetric (D : D7) : Prop := adm1 D → Conclusion0 D → Conclusion1 D

def HodgeTateFromSandwich (D : D7) : Prop := Conclusion2 D

def TowerRallisLemma (D : D7) : Prop := Conclusion0 D → PointsLemma D

def ThetaChernBoundOfLastLine (D : D7) : Prop := adm2 → Conclusion1 D → Conclusion2 D → PointsLemma D → Conclusion4 D

def GGFromIrreducibility (D : D7) : Prop := adm1 D → adm3 D → Conclusion0 D → Conclusion2 D → Conclusion5 D

theorem local_statement_of_parts (D : D7) (h0 : HarishChandraFormulaStatement D) (h1 : IntegralityFromMetric D) (h2 : HodgeTateFromSandwich D) (h3 : TowerRallisLemma D) (h4 : ThetaChernBoundOfLastLine D)
    (h5 : GGFromIrreducibility D) : Stmt D := by
  rintro ⟨a1, a2, a3⟩
  have p0 := h0
  have p1 := h1 a1 p0
  have p3 := h3 p0
  exact ⟨p0, p1, h2, p3, h4 a2 p1 h2 p3, h5 a1 a3 p0 h2⟩

section Fam
variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def admF1 : Prop := ∀ x (i : Fm.Ix x), adm1 (Fm.D x i)

def admF2 : Prop := adm2

def admF3 : Prop := ∀ x (i : Fm.Ix x), adm3 (Fm.D x i)

def FamilyLowestKTypeFormula : Prop := ∀ x (i : Fm.Ix x), Conclusion0 (Fm.D x i)

def ConclusionF1 : Prop := ∀ x (i : Fm.Ix x), Conclusion1 (Fm.D x i)

def ConclusionF2 : Prop := ∀ x (i : Fm.Ix x), Conclusion2 (Fm.D x i)

def ConclusionF3 : Prop := ∀ x (i : Fm.Ix x), PointsLemma (Fm.D x i)

def FamilyEstimateFour : Prop := ∀ x (i : Fm.Ix x), Conclusion4 (Fm.D x i)

def ConclusionF5 : Prop := ∀ x (i : Fm.Ix x), Conclusion5 (Fm.D x i)

def FamilyGlobalFormulaStatement : Prop := ∀ x (i : Fm.Ix x), TwistTheoremAtIndex (Fm.D x i)

def AdmF : Prop := admF1 Fm ∧ admF2 ∧ admF3 Fm

def ConclusionOnFamily : Prop := FamilyLowestKTypeFormula Fm ∧ ConclusionF1 Fm ∧ ConclusionF2 Fm ∧ ConclusionF3 Fm ∧ FamilyEstimateFour Fm ∧ ConclusionF5 Fm

def KudlaFamilyStatement : Prop := AdmF Fm → ConclusionOnFamily Fm

def FamilyFormulaStatement : Prop := FamilyLowestKTypeFormula Fm

def PeriodFamilyStatement : Prop := admF1 Fm → FamilyLowestKTypeFormula Fm → ConclusionF1 Fm

def DeterminantValueFamily : Prop := ConclusionF2 Fm

def FlatLineDegreeFamilyStatement : Prop := FamilyLowestKTypeFormula Fm → ConclusionF3 Fm

def LiftNormFamilyStatement : Prop := admF2 → ConclusionF1 Fm → ConclusionF2 Fm → ConclusionF3 Fm → FamilyEstimateFour Fm

def DegreeBoundFamilyStatement : Prop := admF1 Fm → admF3 Fm → FamilyLowestKTypeFormula Fm → ConclusionF2 Fm → ConclusionF5 Fm

theorem family_statement_of_components (h0 : FamilyFormulaStatement Fm) (h1 : PeriodFamilyStatement Fm) (h2 : DeterminantValueFamily Fm) (h3 : FlatLineDegreeFamilyStatement Fm) (h4 : LiftNormFamilyStatement Fm)
    (h5 : DegreeBoundFamilyStatement Fm) : KudlaFamilyStatement Fm := by
  rintro ⟨a1, a2, a3⟩
  have p0 := h0
  have p1 := h1 a1 p0
  have p3 := h3 p0
  exact ⟨p0, p1, h2, p3, h4 a2 p1 h2 p3, h5 a1 a3 p0 h2⟩

end Fam

end Formalism.MainNotions.VanishingOnXAndXPlusGlobal

end
