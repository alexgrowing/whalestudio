import Mathlib
import Formalism.PeriodIntegrals.VolSemiDirect
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ClosedStep

noncomputable section

namespace PI.VolSemiDirect.W.Cj

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

def HasStableRangeOne (A : Type) [CommRing A] : Prop :=
  ∀ a b x y : A, a * x + b * y = 1 → ∃ t, IsUnit (a + t * b)

def AdeleStableRankOne : Prop := ∀ (F : Type) [Field F] [NumberField F], HasStableRangeOne (AF F)

def ElimSR1 : Prop :=
  ∀ (A : Type) [CommRing A], HasStableRangeOne A → ∀ (k : ℕ) (X : GL (Fin k) A),
    X ∈ Subgroup.closure ({g : GL (Fin k) A | ∃ i j c, i ≠ j ∧
      (g : Matrix (Fin k) (Fin k) A) = Matrix.transvection i j c} ∪
      {g | ∃ d : Fin k → A, (g : Matrix (Fin k) (Fin k) A) = Matrix.diagonal d})

def TransvHaar : Prop :=
  ∀ (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [LocallyCompactSpace A]
    [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A] (k : ℕ)
    (i j : Fin k), i ≠ j → ∀ (c : A) (μ : Measure (Fin k → A)), μ.IsAddHaarMeasure →
      μ.map (Matrix.mulVec (Matrix.transvection i j c)) = μ

def OrthInv : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (k : ℕ) (G X : Matrix (Fin k) (Fin k) (AF F)),
    IsUnit G.det → X.transpose * G * X = G →
    ∀ μ : Measure (Fin k → AF F), μ.IsAddHaarMeasure → μ.map (Matrix.mulVec X) = μ

def VMod : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (g : HA (AF F) σ J) (μ : Measure (Fin M → AF F ⊗[F] E)), μ.IsAddHaarMeasure →
      μ.map (lin (AF F) σ J g) = μ

end PI.VolSemiDirect.W.Cj
