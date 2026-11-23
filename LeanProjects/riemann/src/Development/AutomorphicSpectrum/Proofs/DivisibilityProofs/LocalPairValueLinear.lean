import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SumSupportEq
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EventualValue
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocPairValLinear
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.ValLin

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [DecidableEq K]
  {ι : K → Type} {σ : Type}

end GlobalTheory.CompanionTheory.Ar.Num.ValLin

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem locPair_val_linear : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) [Fintype σ] (T : LocPair ι O σ) (P : Ideal (MRing ι O)), (∀ Gs Hs, T.val P (Gs + Hs) = T.val P Gs + T.val P Hs) ∧ (∀ (c : ℝ) Gs, T.val P (fun i => C c * Gs i) = c * T.val P Gs) ∧ ∀ (α : Type) (s : Finset α) (Gs : α → σ → MvPolynomial (σ ⊕ σ) ℝ), T.val P (fun i => ∑ a ∈ s, Gs a i) = ∑ a ∈ s, T.val P (Gs a) :=
  _root_.UpperTheory.Reformulated.B.Qp9.locPair_val_linear

end GlobalTheory.CompanionTheory.Ar.Num
