import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdmissibleUnitaryKFinite

noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.LinRed

namespace GlobalTheory.CompanionTheory.Hypotheses₂

namespace HCSS

variable {n : ℕ}

def centre (G : Set (Matrix (Fin n) (Fin n) ℂ)) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {z | z ∈ G ∧ ∀ g ∈ G, z * g = g * z}

def IsLinSS (G : Set (Matrix (Fin n) (Fin n) ℂ)) : Prop := IsLinRed G ∧ (centre G).Finite

def lieOf (G : Set (Matrix (Fin n) (Fin n) ℂ)) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {X | ∀ t : ℝ, NormedSpace.exp (t • X) ∈ G}

def centralTorus (G : Set (Matrix (Fin n) (Fin n) ℂ)) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {d | ∃ C ∈ lieOf (maxCpt G), (∀ Y ∈ lieOf (maxCpt G), C * Y = Y * C) ∧ d = NormedSpace.exp C}

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsPermissible (G : Set (Matrix (Fin n) (Fin n) ℂ)) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ z ∈ centralTorus G ∩ centre G, ∃ c : ℂ, π z = c • (1 : H →L[ℂ] H)

def IsWellBehaved (G : Set (Matrix (Fin n) (Fin n) ℂ)) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H) : Prop :=
  ∀ g₀ ∈ G, ∃ (U : Set (Fin n → Fin n → ℂ)) (F : (Fin n → Fin n → ℂ) → H),
    IsOpen U ∧ Matrix.of.symm g₀ ∈ U ∧ AnalyticOnNhd ℝ F U ∧ ∀ z ∈ U, Matrix.of z ∈ G → π (Matrix.of z) v = F z

def IsLieStable (G : Set (Matrix (Fin n) (Fin n) ℂ)) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (S : Submodule ℂ H) : Prop :=
  ∀ X ∈ lieOf G, ∀ v ∈ S, ∃ v' ∈ S, HasDerivAt (fun t : ℝ => π (NormedSpace.exp (t • X)) v) v' 0

def KFiniteWellBehaved : Prop :=
  ∀ (n : ℕ) (G : Set (Matrix (Fin n) (Fin n) ℂ)), IsLinSS G →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsAdmOn G π → IsPermissible G π →
      ∀ v : H, IsKFinOn G π v → IsWellBehaved G π v

def ClosureStable : Prop :=
  ∀ (n : ℕ) (G : Set (Matrix (Fin n) (Fin n) ℂ)), IsLinSS G →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsAdmOn G π → IsPermissible G π →
      ∀ S : Submodule ℂ H, (∀ v ∈ S, IsKFinOn G π v) → IsLieStable G π S →
        ∀ g ∈ G, ∀ v ∈ S.topologicalClosure, π g v ∈ S.topologicalClosure

def UnitaryAdmissible : Prop :=
  ∀ (n : ℕ) (G : Set (Matrix (Fin n) (Fin n) ℂ)), IsLinSS G →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn G σ → IsIrredOn G σ → IsAdmOn G σ

end HCSS

def HCSemisimple : Prop := HCSS.KFiniteWellBehaved ∧ HCSS.ClosureStable ∧ HCSS.UnitaryAdmissible

namespace HCSS

variable {n : ℕ}

def SUJset (ε : Fin n → Bool) : Set (Matrix (Fin n) (Fin n) ℂ) := {g | g ∈ UJset ε ∧ g.det = 1}

def stdRep (n : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) : EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n) :=
  Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) g

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {G : Set (Matrix (Fin n) (Fin n) ℂ)}
  {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

end HCSS

end GlobalTheory.CompanionTheory.Hypotheses₂

end
