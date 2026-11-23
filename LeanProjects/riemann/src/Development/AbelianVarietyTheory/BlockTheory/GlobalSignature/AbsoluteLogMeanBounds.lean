import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.LatticeIntegralCoordinates

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AbsoluteLogMeanBounds

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients Classical

def mean (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (X : (M →ₐ[ℚ] ℂ) → ℝ) : ℝ :=
  (∑ ρ : M →ₐ[ℚ] ℂ, X ρ) / (Module.finrank ℚ M : ℝ)

def th0NormSq (Λ : AddSubgroup ℂ) (t : ℂ) : ℝ := normSq1 Λ (th0 Λ t)

def IsConjugateCurvePointLift (D : D7) (Λ : AddSubgroup ℂ) (M : IntermediateField ℚ ℂ) (t : (M →ₐ[ℚ] ℂ) → ℂ) : Prop :=
  ∀ ρ, IsTwoTorsionPointUnkilled D (lamConj M ρ Λ) (t ρ)

def meanLog (Λ : AddSubgroup ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M]
    (t : (M →ₐ[ℚ] ℂ) → ℂ) : ℝ :=
  mean M fun ρ => Real.log (th0NormSq (lamConj M ρ Λ) (t ρ))

def meanLogPos (Λ : AddSubgroup ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M]
    (t : (M →ₐ[ℚ] ℂ) → ℂ) : ℝ :=
  mean M fun ρ => max (Real.log (th0NormSq (lamConj M ρ Λ) (t ρ))) 0

def kronBound (D : D7) : ℝ :=
  (1 / 2) * (Real.log (Real.sqrt (D.host.d : ℝ)) - Real.eulerMascheroniConstant + logDerivativeAtOne D)

def HidaSetting (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ)
    (t : (M →ₐ[ℚ] ℂ) → ℂ) : Prop :=
  IsCurveIdeal D cc ∧ IsDiscriminantTwelfthRootOfIdealLattice D cc δ ∧ DataIn D (tor0 D cc δ) M ∧ IsConjugateCurvePointLift D (lamOf D cc δ) M t

def SignedMean : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M]
    (t : (M →ₐ[ℚ] ℂ) → ℂ), HidaSetting D cc δ M t →
    meanLog (lamOf D cc δ) M t ≤ kronBound D ∧
    ∀ L : ℝ, Real.log D.host.rdE + |logDerivativeAtOne D| ≤ 2 * L →
      kronBound D ≤ L ∧ meanLog (lamOf D cc δ) M t ≤ L

def AbsoluteMean : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M]
      (t : (M →ₐ[ℚ] ℂ) → ℂ), HidaSetting D cc δ M t →
      ∀ Lsc : ℝ, Real.log D.host.v + |logDerivativeAtOne D| ≤ Lsc →
        meanLog (lamOf D cc δ) M t ≤ C * Lsc ∧ meanLogPos (lamOf D cc δ) M t ≤ C * Lsc

def ThetaNullMean : Prop := SignedMean ∧ AbsoluteMean

def Guards : Prop :=
  ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ),
    IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → DataIn D (tor0 D cc δ) M →
    ∀ ρ : M →ₐ[ℚ] ℂ, (∃ t, IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t) ∧
      ∀ t, IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t →
        0 < th0NormSq (lamConj M ρ (lamOf D cc δ)) t ∧
        ∀ t', IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t' →
          th0 (lamConj M ρ (lamOf D cc δ)) t' = th0 (lamConj M ρ (lamOf D cc δ)) t

def PositivePart : Prop :=
  ∃ C : ℝ, ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ), HidaSetting D cc δ M t →
    (∀ ρ, -(1 / 4) * Real.log (D.host.d : ℝ) - C ≤
      Real.log (th0NormSq (lamConj M ρ (lamOf D cc δ)) (t ρ))) ∧
    meanLogPos (lamOf D cc δ) M t ≤ kronBound D + (1 / 4) * Real.log (D.host.d : ℝ) + C

end GlobalTheory.IndefiniteRowSideFullHecke.AbsoluteLogMeanBounds
