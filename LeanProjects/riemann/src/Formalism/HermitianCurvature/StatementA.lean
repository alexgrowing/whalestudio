import Formalism.DoubleCosetMeasures.Statement

namespace Formalism.FourierDecayAlt.A

open Formalism.DoubleCosetMeasures MeasureTheory

def LevelOneKernelPoint : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (l : List ℕ) (t : ℕ → Kˣ) (ψ : AddChar K ℂ) (C : Type) [AddCommGroup C] [Module R C] (e : C)
    (lam : C →ₗ[R] KR R) (μ₁ : Measure (lowW K (l ++ [1]) t))
    (μ₂ : Measure (upUniG K (l ++ [1]).sum)),
    BB R (l ++ [1]) t ψ C e lam μ₁ μ₂ ≠ 0 →
      lam e = Submodule.Quotient.mk (((t l.length)⁻¹ : Kˣ) : K)

def LevelOneKernelPair : Prop :=
  ∀ (K : Type) [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] (R : Subring K)
    (l l' : List ℕ) (t t' : ℕ → Kˣ) (ψ : AddChar K ℂ)
    (C : Type) [AddCommGroup C] [Module R C] (e : C) (lam : C →ₗ[R] KR R)
    (μ₁ : Measure (lowW K (l ++ [1]) t)) (μ₂ : Measure (upUniG K (l ++ [1]).sum))
    (μ₁' : Measure (lowW K (l' ++ [1]) t')) (μ₂' : Measure (upUniG K (l' ++ [1]).sum)),
    BB R (l ++ [1]) t ψ C e lam μ₁ μ₂ ≠ 0 → BB R (l' ++ [1]) t' ψ C e lam μ₁' μ₂' ≠ 0 →
      (((t l.length)⁻¹ : Kˣ) : K) - (((t' l'.length)⁻¹ : Kˣ) : K) ∈ R

end Formalism.FourierDecayAlt.A
