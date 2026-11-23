import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk

theorem coefClause_of_thetaClause : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (om : WRep A B) (omh : WRep (dblSp A) B), IsWeilDatumO ψ A B χA χB om → ThetaClause ψ A B χB om omh → ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 → CoefClause ψ A B om omh ν 𝓕 := by
  intro D ψ A B χA χB om omh _ hT ν 𝓕 _ f₁ f₂ h₁ h₂
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.evZero_delta A B ν 𝓕 f₁ f₂, fun g => ?_⟩
  have h := ((hT f₁ f₂ h₁ h₂).2 g 1 1).1
  have h1 : om ((1 : GA D A), (1 : GA D B)) f₂ = f₂ := by
    rw [show ((1 : GA D A), (1 : GA D B)) = (1 : GA D A × GA D B) from rfl, map_one]; rfl
  have hd : detA A (1 : GA D A) = 1 := map_one _
  rw [h1, hd, map_one, inv_one, Circle.coe_one, one_smul] at h
  simp only [swSec]
  rw [h, GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.evZero_delta]

end GlobalTheory.Core.Rk
