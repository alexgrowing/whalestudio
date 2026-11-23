import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.WeilQuad

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

def Hyp (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ) : Prop :=
  IsField A.K ∧ IsField A.L ∧ IsStdChar ψ ∧ SelfDual μ (A.kerL ψ x) ∧
    ∀ s : A.Kˣ, ((∃ y, A.NL y = s) → ω s = 1) ∧ ((¬ ∃ y, A.NL y = s) → ω s = -1)

def nOp (A : Et F E) (ψ : AddChar F ℂ) (x z : A.K) (φ : A.L → ℂ) : A.L → ℂ :=
  fun y => A.psiK ψ (z * x * A.NL y) * φ y

def mOp (A : Et F E) (ω : A.K → ℂ) (s : A.Kˣ) (φ : A.L → ℂ) : A.L → ℂ :=
  fun y => ω s * (A.absK s : ℂ) * φ ((s : A.K) • y)

def fOp (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (μ : Measure A.L) (φ : A.L → ℂ) : A.L → ℂ :=
  fourB μ (A.kerL ψ x) φ

def gaussInt (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (μ : Measure A.L) (u : A.K) (S : Set A.L) : ℂ :=
  ∫ y in S, A.psiK ψ (u * x * A.NL y) ∂μ

def IsStableGauss (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (μ : Measure A.L) (u : A.K) (G : ℂ) : Prop :=
  ∃ Λ₀ : AddSubgroup A.L, IsOpen (Λ₀ : Set A.L) ∧ IsCompact (Λ₀ : Set A.L) ∧
    ∀ Λ : AddSubgroup A.L, IsOpen (Λ : Set A.L) → IsCompact (Λ : Set A.L) → Λ₀ ≤ Λ →
      gaussInt A ψ x μ u Λ = G

end GlobalTheory.JR.WeilQuad
