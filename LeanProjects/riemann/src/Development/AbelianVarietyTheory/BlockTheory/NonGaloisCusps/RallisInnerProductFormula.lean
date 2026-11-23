import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedSmooth

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory

namespace GlobalTheory.IndefiniteRowSideFullHecke.RallisInnerProductFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def prodFun {X : Type} (a b : X → ℂ) : X → ℂ := fun x => a x * starRingEnd ℂ (b x)

def prodOn {X : Type} [MeasurableSpace X] (μ : Measure X) (𝓕 : Set X) (a b : X → ℂ) : ℂ :=
  ∫ x in 𝓕, prodFun a b x ∂μ

variable {V W : HSp D}

def liftFun (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (φ : WO V W → ℂ) (f : GA D W → ℂ) (h : GA D V) :
    GA D W → ℂ :=
  fun g => starRingEnd ℂ (thetaKO om h g φ) * f g

def thetaLift (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (μG : Measure (GA D W)) (𝓕G : Set (GA D W))
    (φ : WO V W → ℂ) (f : GA D W → ℂ) : GA D V → ℂ :=
  fun h => ∫ g in 𝓕G, liftFun om φ f h g ∂μG

def doublingFun (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (μX : Measure (WO V W)) (𝓕X : Set (WO V W))
    (μG : Measure (GA D W)) (𝓕G : Set (GA D W)) (φ₁ φ₂ : WO V W → ℂ) (f₁ f₂ : GA D W → ℂ) : GA D W → ℂ :=
  fun g => starRingEnd ℂ (prodOn μX 𝓕X (om (1, g) φ₁) φ₂) * prodOn μG 𝓕G (rTr W g f₁) f₂

structure InnerProductFormula (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))
    (μH : Measure (GA D V)) (𝓕H : Set (GA D V)) (μG : Measure (GA D W)) (𝓕G : Set (GA D W))
    (μX : Measure (WO V W)) (𝓕X : Set (WO V W)) (φ₁ φ₂ : WO V W → ℂ) (f₁ f₂ : GA D W → ℂ) : Prop where

  vol_lt_top : μH 𝓕H < ⊤

  lift₁ : ∀ h, IntegrableOn (liftFun om φ₁ f₁ h) 𝓕G μG

  lift₂ : ∀ h, IntegrableOn (liftFun om φ₂ f₂ h) 𝓕G μG

  left : IntegrableOn (prodFun (thetaLift om μG 𝓕G φ₁ f₁) (thetaLift om μG 𝓕G φ₂ f₂)) 𝓕H μH

  coefWeil : ∀ g, IntegrableOn (prodFun (om (1, g) φ₁) φ₂) 𝓕X μX

  coefCusp : ∀ g, IntegrableOn (prodFun (rTr W g f₁) f₂) 𝓕G μG

  right : Integrable (doublingFun om μX 𝓕X μG 𝓕G φ₁ φ₂ f₁ f₂) μG

  formula : prodOn μH 𝓕H (thetaLift om μG 𝓕G φ₁ f₁) (thetaLift om μG 𝓕G φ₂ f₂) =
    (((μH 𝓕H).toReal : ℝ) : ℂ) * ∫ g, doublingFun om μX 𝓕X μG 𝓕G φ₁ φ₂ f₁ f₂ g ∂μG

def RallisInnerProduct (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle)
    (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)),
    V.SigOK → V.IsPosDef → 2 * W.rank < V.rank → IsWeilDatumO ψ V W χV χW om →
    ∀ (μH : Measure (GA D V)) (𝓕H : Set (GA D V)), μH.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕H μH →
    ∀ (μG : Measure (GA D W)) (𝓕G : Set (GA D W)), μG.IsHaarMeasure → IsFundamentalDomain (GQ W) 𝓕G μG →
    ∀ (μX : Measure (WO V W)) (𝓕X : Set (WO V W)), IsCovolOne (ratL W V) μX 𝓕X →
    ∀ φ₁ φ₂ : WO V W → ℂ, IsThetaFunO ψ V W φ₁ → IsThetaFunO ψ V W φ₂ →
    ∀ θ : InfFam D, IsInfFam θ →
    ∀ f₁ f₂ : GA D W → ℂ, IsAutFunSm θ W f₁ → IsCuspFun W f₁ → IsAutFunSm θ W f₂ → IsCuspFun W f₂ →
      InnerProductFormula om μH 𝓕H μG 𝓕G μX 𝓕X φ₁ φ₂ f₁ f₂

end GlobalTheory.IndefiniteRowSideFullHecke.RallisInnerProductFormula

end
