import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

open NumberField

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AutomorphicBallCount

open Formalism.MainNotions.S GlobalTheory.Count

def ballSet (I : AutInst) (x : I.GA) (r : InfinitePlace I.F → ℝ) : Set I.GA :=
  {γ | γ ∈ I.GFset ∧ (x⁻¹ * γ * x).2 ∈ I.Kset ∧ ∀ v, dHS (uMat ((x⁻¹ * γ * x).1 v)) ≤ r v}

def bigA (I : AutInst) (x : I.GA) : ℝ :=
  (3 * Real.sqrt (I.n : ℝ) / (tau1 I x) ^ 2) ^ (2 * (I.n ^ 2 * I.f))

def AutBallCount : Prop :=
  ∀ (I : AutInst), 1 ≤ I.n → ∀ (x : I.GA) (r : InfinitePlace I.F → ℝ), (∀ v, 0 ≤ r v) →
    (ballSet I x r).Finite ∧
      ((ballSet I x r).ncard : ℝ) ≤ bigA I x * Real.exp (2 * (I.n : ℝ) ^ 2 * ∑ v, r v)

end GlobalTheory.IndefiniteRowSideFullHecke.AutomorphicBallCount
