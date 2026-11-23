import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.AmpNZCut
import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Transported

open MeasureTheory
open scoped ENNReal InnerProductSpace

noncomputable section

namespace Formalism.MainNotions.S.Pv.BetaCut

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

def coefM {k r : ℕ} {H Wp Wq : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (v v' : H) (ξ : Wp) (ξ' : Wq)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Wq →L[ℂ] Wp :=
  (innerSL ℂ ξ').smulRight (⟪v, σ g v'⟫_ℂ • ξ)

def CoefInCC : Prop :=
  ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (h : ℝ) (m : ℕ) (A : ℝ),
    IsHCParam lam → PI.UpqRep.IsDSHpk k r ε lam σ → GapAtLeast ε lam h → ReciprocityTheory.ChartRestriction.DS.thrStar ε + m < h → A ≤ m →
    ∀ v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ, ∀ v' ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ,
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
      (ξ : Wp) (ξ' : Wq), Formalism.FourierDecayAlt.B.InCC (k := k) (r := r) A 5 (coefM σ v v' ξ ξ')

def BetaInfCoefNZ : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq)
    (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (h : ℝ),
    IsHCParam lam → PI.UpqRep.IsDSHpk k r ε lam σ → GapAtLeast ε lam h → Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h →
    ∀ (v v' : H) (l : H → Wp) (l' : H → Wq) (ξ : Wp) (ξ' : Wq),
      v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ → v' ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ →
      Formalism.FourierDecayAlt.ThreeDimData.be D.z Formalism.QuantumDeterminants.cStd D.π σ D.μW D.μN v v = (innerSL ℂ (l v)).smulRight (l v) →
      Formalism.FourierDecayAlt.ThreeDimData.be D.z' Formalism.QuantumDeterminants.cStd D.π' σ D.μW' D.μN v' v' = (innerSL ℂ (l' v')).smulRight (l' v') →
      ⟪l v, ξ⟫_ℂ ≠ 0 → ⟪ξ', l' v'⟫_ℂ ≠ 0 →
      Formalism.FourierDecayAlt.B.betaInf D (coefM σ v v' ξ ξ') (coefM σ v v' ξ ξ') ≠ 0

end Formalism.MainNotions.S.Pv.BetaCut
