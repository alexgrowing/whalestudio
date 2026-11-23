import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.LatticeIntegralCoordinates

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients

def conjNormSq (M : IntermediateField ℚ ℂ) (Λ : AddSubgroup ℂ) (ρ : M →ₐ[ℚ] ℂ) (t : ℂ) : ℝ :=
  normSq1 (lamConj M ρ Λ) (th0 (lamConj M ρ Λ) t)

def meanLog (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (Λ : AddSubgroup ℂ)
    (t : (M →ₐ[ℚ] ℂ) → ℂ) : ℝ :=
  (∑ ρ : M →ₐ[ℚ] ℂ, Real.log (conjNormSq M Λ ρ (t ρ))) / (Module.finrank ℚ M : ℝ)

def meanPosLog (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] (Λ : AddSubgroup ℂ)
    (t : (M →ₐ[ℚ] ℂ) → ℂ) : ℝ :=
  (∑ ρ : M →ₐ[ℚ] ℂ, max 0 (Real.log (conjNormSq M Λ ρ (t ρ)))) / (Module.finrank ℚ M : ℝ)

def HidaSetting (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ)
    (t : (M →ₐ[ℚ] ℂ) → ℂ) : Prop :=
  IsCurveIdeal D cc ∧ IsDiscriminantTwelfthRootOfIdealLattice D cc δ ∧ DataIn D (tor0 D cc δ) M ∧
    ∀ ρ : M →ₐ[ℚ] ℂ, IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) (t ρ)

def bound (D : D7) : ℝ :=
  (1 / 2) * (Real.log (Real.sqrt D.host.d) - Real.eulerMascheroniConstant + logDerivativeAtOne D)

def SignedMean (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M]
    (t : (M →ₐ[ℚ] ℂ) → ℂ), HidaSetting D cc δ M t → meanLog M (lamOf D cc δ) t ≤ bound D

def MeanLeL (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M]
    (t : (M →ₐ[ℚ] ℂ) → ℂ), HidaSetting D cc δ M t →
    ∀ L : ℝ, Real.log D.host.rdE + |logDerivativeAtOne D| ≤ 2 * L → meanLog M (lamOf D cc δ) t ≤ L

def MeanLeC (C : ℝ) (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M]
    (t : (M →ₐ[ℚ] ℂ) → ℂ), HidaSetting D cc δ M t →
    ∀ L : ℝ, Real.log D.host.v + |logDerivativeAtOne D| ≤ L → meanLog M (lamOf D cc δ) t ≤ C * L

def PosMean (C : ℝ) (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M]
    (t : (M →ₐ[ℚ] ℂ) → ℂ), HidaSetting D cc δ M t →
    meanPosLog M (lamOf D cc δ) t ≤ bound D + (1 / 4) * Real.log D.host.d + C

def PosMeanLeC (C : ℝ) (D : D7) : Prop :=
  ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M]
    (t : (M →ₐ[ℚ] ℂ) → ℂ), HidaSetting D cc δ M t →
    ∀ L : ℝ, Real.log D.host.v + |logDerivativeAtOne D| ≤ L → meanPosLog M (lamOf D cc δ) t ≤ C * L

def Theta0SignedMean : Prop :=
  (∀ D : D7, SignedMean D) ∧ (∀ D : D7, MeanLeL D) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ D : D7, MeanLeC C D

def Theta0PosMean : Prop :=
  (∃ C : ℝ, 0 ≤ C ∧ ∀ D : D7, PosMean C D) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ D : D7, PosMeanLeC C D

def Theta0Mean : Prop := Theta0SignedMean ∧ Theta0PosMean

example (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] :
    Fintype.card (M →ₐ[ℚ] ℂ) = Module.finrank ℚ M ∧ 0 < Module.finrank ℚ M :=
  ⟨AlgHom.card ℚ M ℂ, Module.finrank_pos⟩

end GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans
