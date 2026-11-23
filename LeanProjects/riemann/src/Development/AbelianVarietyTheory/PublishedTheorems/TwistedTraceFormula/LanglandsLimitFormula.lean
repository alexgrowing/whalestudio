import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic

noncomputable section

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

namespace GlobalTheory.Published

def LanglandsLimitFormula : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (D : Datum ε), D.Positive → ∀ ν' : Measure (UJ ε), IsHaarSub D.Nbar ν' →
    ∀ c : ℝ, (∀ φ ∈ indFun ⊤ D.j D.W (fun _ => (1 : ℂ →L[ℂ] ℂ)) (rho n D.j),
        Integrable φ ν' ∧ ∫ k : KG ε, φ k ∂muK ε = c * ∫ u, φ u ∂ν') →
      ∀ f ∈ D.fns, IsKFinFun f → ∀ f' ∈ D.dualFns, IsKFinFun f' → ∀ x, InChamber x →
        ∀ t : ℝ → UJ ε, (∀ r, IsSplit ε D.W (r • x) (t r)) →
          Integrable (fun u => ⟪f' 1, f u⟫_ℂ) ν' ∧
          Tendsto (fun r : ℝ => Complex.exp (r * pairing D.j (rho n D.j - D.s) x) *
              ∫ k : KG ε, ⟪f' k, f (k * t r)⟫_ℂ ∂muK ε) atTop (𝓝 (c * ∫ u, ⟪f' 1, f u⟫_ℂ ∂ν'))

end GlobalTheory.Published

end
