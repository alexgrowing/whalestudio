import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilCorrespond
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DecayZero

noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.WeilM Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ContDiff

namespace GlobalTheory.CompanionTheory.ThetaCoord

variable {F : Type} [Field F] [NumberField F] {κ : Type}

variable (F κ) in

abbrev Pt : Type := (κ → AF F) × (κ → AF F)

def ratPt (γ : (κ → F) × (κ → F)) : Pt F κ :=
  (fun i => algebraMap F (AF F) (γ.1 i), fun i => algebraMap F (AF F) (γ.2 i))

def form [Fintype κ] (w w' : Pt F κ) : AF F := w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2

def IsFinPt (w : Pt F κ) : Prop := ∀ i, (w.1 i).1 = 0 ∧ (w.2 i).1 = 0

def IsInfPt (w : Pt F κ) : Prop := ∀ i, (w.1 i).2 = 0 ∧ (w.2 i).2 = 0

def heisC [Fintype κ] (ψ : AddChar (AF F) ℂ) (u : Pt F κ) (T : Pt F κ → ℂ) : Pt F κ → ℂ :=
  fun w => ψ (⅟(2 : AF F) * form w u) * T (w + u)

structure IsThetaC [Fintype κ] (ψ : AddChar (AF F) ℂ) (T : Pt F κ → ℂ) : Prop where

  quasi : ∀ γ w, T (ratPt γ + w) = ψ (-(⅟(2 : AF F) * form (ratPt γ) w)) * T w

  level : ∃ U : AddSubgroup (Pt F κ), IsOpen (U : Set (Pt F κ)) ∧ ∀ u ∈ U, IsFinPt u → heisC ψ u T = T
  cont : Continuous T

  smooth : ∀ (k : ℕ) (L : (Fin k → ℝ) →+ Pt F κ), Continuous L → (∀ t, IsInfPt (L t)) →
    ∀ w, ContDiff ℝ ∞ fun t => T (w + L t)

def thetaC [Fintype κ] (ψ : AddChar (AF F) ℂ) (Φ : (κ → AF F) → ℂ) (w : Pt F κ) : ℂ :=
  thetaSum F (schr ψ w Φ)

variable (F κ) in

def ratSub : AddSubgroup (κ → AF F) :=
  ((algebraMap F (AF F)).toAddMonoidHom.compLeft κ).range

structure IsUnitDom [Fintype κ] (μ : Measure (κ → AF F)) (𝓓 : Set (κ → AF F)) : Prop where
  haar : μ.IsAddHaarMeasure
  meas : MeasurableSet 𝓓
  dom : IsAddFundamentalDomain (ratSub F κ) 𝓓 μ
  mass : μ 𝓓 = 1

def zakC [Fintype κ] (ψ : AddChar (AF F) ℂ) (μ : Measure (κ → AF F)) (𝓓 : Set (κ → AF F)) (T : Pt F κ → ℂ)
    (a : κ → AF F) : ℂ :=
  ∫ b in 𝓓, ψ (-(⅟(2 : AF F) * (a ⬝ᵥ b))) * T (a, b) ∂μ

def joinPt (x : κ → mixedEmbedding.mixedSpace F) (y : κ → FiniteAdeleRing (𝓞 F) F) : κ → AF F :=
  fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x i), y i)

def finOf (a : κ → AF F) : κ → FiniteAdeleRing (𝓞 F) F := fun i => (a i).2

def infOf (a : κ → AF F) : κ → mixedEmbedding.mixedSpace F :=
  fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (a i).1

end GlobalTheory.CompanionTheory.ThetaCoord

end
