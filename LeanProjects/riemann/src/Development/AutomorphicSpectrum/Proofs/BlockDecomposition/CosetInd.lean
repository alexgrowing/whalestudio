import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open scoped NumberField.AdeleRing ValuativeRel

namespace GlobalTheory.CompanionTheory.WS

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def rowAct (h : GL (Fin 2) F) (v : F × F) : F × F :=
  (v.1 * h.val 0 0 + v.2 * h.val 1 0, v.1 * h.val 0 1 + v.2 * h.val 1 1)

def IsSB (Ψ : F × F → ℂ) : Prop := IsLocallyConstant Ψ ∧ HasCompactSupport Ψ

def pF (χ : AddChar F Circle) (Φ : F × F → ℂ) (p : F × F) : ℂ :=
  ∫ t, Φ (p.1, t) * (χ (p.2 * t) : ℂ) ∂selfDualMeasure χ

def inn (χ : AddChar F Circle) (Ψ : F × F → ℂ) (u : Fˣ) : ℂ :=
  ∫ y, Ψ ((u : F), (u : F) * y) * (χ (-y) : ℂ) ∂selfDualMeasure χ

def den (χ : AddChar F Circle) (c₁ c₂ : Fˣ →* ℂˣ) (Ψ : F × F → ℂ) (u : Fˣ) : ℂ :=
  ((c₁ u : ℂˣ) : ℂ) * (((c₂ u)⁻¹ : ℂˣ) : ℂ) * mp u 1 * inn χ Ψ u

def lin (χ : AddChar F Circle) (c₁ c₂ : Fˣ →* ℂˣ) (Ψ : F × F → ℂ) : ℂ :=
  ∫ u : Fˣ, den χ c₁ c₂ Ψ u ∂multHaar F

def WL (χ : AddChar F Circle) (c₁ c₂ : Fˣ →* ℂˣ) (Ψ : F × F → ℂ) (g : GL (Fin 2) F) : ℂ :=
  ((c₁ (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) * mp (Matrix.GeneralLinearGroup.det g) (1 / 2) *
    lin χ c₁ c₂ (Ψ ∘ rowAct g)

variable (F) in

def Ln (n : ℤ) : Set (F × F) := {v | v.1 ∈ valBall F n ∧ v.2 ∈ valBall F n}

def cosetInd (n : ℤ) (x : F × F) : F × F → ℂ := Set.indicator {v | v - x ∈ Ln F n} 1

def spanSet (n : ℤ) (x : F × F) : Set (F × F) := {v | ∃ a ∈ 𝒪[F], v - (a • x) ∈ Ln F n}

variable (F) in

def lat0 : F × F → ℂ := Set.indicator (Ln F 0) 1

end GlobalTheory.CompanionTheory.WS
