import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
open NumberField IsDedekindDomain MeasureTheory Topology GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.SmallSec

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

variable (F) in

def secSet (m : ℕ) : Set (Matrix (Fin 2) (Fin 3) F) :=
  {X | X 0 0 - 1 ∈ valBall F (m : ℤ) ∧ X 0 1 ∈ valBall F (m : ℤ) ∧ X 1 0 ∈ valBall F (m : ℤ) ∧
    X 1 1 - 1 ∈ valBall F (m : ℤ) ∧ X 0 2 ∈ valBall F (-(m : ℤ)) ∧ X 1 2 ∈ valBall F (-(m : ℤ))}

def secFun (ψ : AddChar F Circle) (m : ℕ) : Matrix (Fin 2) (Fin 3) F → ℂ :=
  (secSet F m).indicator fun X => (ψ (X 1 2) : ℂ)

variable (F) in

def torF (n : ℕ) : F → ℂ := ({x : F | x - 1 ∈ valBall F (n : ℤ)} : Set F).indicator 1

def torG (ψ : AddChar F Circle) (n : ℕ) : F → ℂ :=
  (valBall F (-(n : ℤ)) : Set F).indicator fun r => (ψ r : ℂ)

end GlobalTheory.CompanionTheory.SmallSec
