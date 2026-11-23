import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.RaisingLoweringNormIdentities
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EqZeroOfDatumEmbeddingEqZero

noncomputable section

open Finset Matrix MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base

open ReciprocityTheory.ChartRestriction.DS

def PsiForStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (h : ℝ) (T : S7.KType ε (lowK ε lam)) (μ : Fin n → ℤ),
    S7.IsHCParam lam → S7.IsMu lam μ → GapAtLeast ε lam h → 1 ≤ S7.q0 ε → 8 * (n : ℝ) * S7.q0 ε < h →
    IsPsiFor ε lam T (S7.PsiM T μ) ∧ ContinuousOn (S7.PsiM T μ) (UJset ε)

def LinkStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : S7.KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), StdGap ε lam → IsPsiFor ε lam T Ψ →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H),
      IsHWSmooth ε σ lam w ∧ ∀ g ∈ UJset ε, ⟪w, σ g w⟫_ℂ = ⟪T.w, Ψ g T.w⟫_ℂ

def AssemblyStatement : Prop :=
  PairingPropertiesStatement → TangentPairingStatement → NsetExpInjectiveSurjective → CayleyMajorantBound → GaussianLimitHaar → ExistsUnitaryHaarProbability →
    WhittakerSchurOrthogonality → LamTStatement → PsiForStatement → LinkStatement → StepIBaseStatement

end ReciprocityTheory.ChartRestriction.DS.Lap.Base
