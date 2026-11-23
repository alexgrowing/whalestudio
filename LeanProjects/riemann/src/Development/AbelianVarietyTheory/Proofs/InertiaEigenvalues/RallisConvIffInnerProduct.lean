import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RallisInnerProductFormula
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMulConjSelf

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.RawLift GlobalTheory.IndefiniteRowSideFullHecke.RallisInnerProductFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Cmp.RallisRange

variable {D : D7} {V W : HSp D}

def Concl (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V))
    (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W))
    (f₁ f₂ : WO V W → ℂ) (φ₁ φ₂ : GA D W → ℂ) : Prop :=
  (∀ h, IntegrableOn (fun g => star (thetaKO om h g f₁) * φ₁ g) 𝓖 νW) ∧
  IntegrableOn (fun h => star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h) 𝓗 νV ∧
  Integrable (fun g => thetaIP μ 𝓕 (om (1, g) f₂) f₁ * ∫ x in 𝓖, star (φ₁ x) * φ₂ (x * g) ∂νW) νW ∧
  ∫ h in 𝓗, star (upLift om νW 𝓖 f₁ φ₁ h) * upLift om νW 𝓖 f₂ φ₂ h ∂νV =
    ((νV 𝓗).toReal : ℂ) * ∫ g, thetaIP μ 𝓕 (om (1, g) f₂) f₁ * (∫ x in 𝓖, star (φ₁ x) * φ₂ (x * g) ∂νW) ∂νW

theorem vol_lt_top (V : HSp D) {ν : Measure (GA D V)} {𝓗 : Set (GA D V)} (hν : ν.IsHaarMeasure)
    (h : IsFundamentalDomain (GQ V) 𝓗 ν) : ν 𝓗 < ⊤ :=
  GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol V ν 𝓗 hν h

def CuspCoefConv (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)),
    V.SigOK → V.IsPosDef → 2 * W.rank < V.rank → IsWeilDatumO ψ V W χV χW om →
    ∀ (μH : Measure (GA D V)) (𝓕H : Set (GA D V)), μH.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕H μH →
    ∀ (μG : Measure (GA D W)) (𝓕G : Set (GA D W)), μG.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕G μG →
    ∀ (μX : Measure (WO V W)) (𝓕X : Set (WO V W)), IsCovolOne (ratL W V) μX 𝓕X →
    ∀ θ : InfFam D, IsInfFam θ →
    ∀ f₁ f₂ : GA D W → ℂ, IsAutFunSm θ W f₁ → IsCuspFun W f₁ → IsAutFunSm θ W f₂ → IsCuspFun W f₂ →
      ∀ g, IntegrableOn (prodFun (rTr W g f₁) f₂) 𝓕G μG

end GlobalTheory.Cmp.RallisRange

end
