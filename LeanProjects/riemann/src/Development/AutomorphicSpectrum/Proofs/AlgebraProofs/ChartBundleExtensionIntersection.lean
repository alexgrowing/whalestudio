import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleExtensionComparisonStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleIntersectionSymmetryStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DvrBundleStatementAStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.QuotAdd

theorem main : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (d N₀ N N₂ : ℕ) (V₀ : Type) [AddCommGroup V₀] [Module Ω V₀] (V : Type) [AddCommGroup V] [Module Ω V] (V₂ : Type) [AddCommGroup V₂] [Module Ω V₂] (A A' : ChartBundle O (mseg x) N₀ V₀) (E E' : ChartBundle O (mseg x) N V) (C C' : ChartBundle O (mseg x) N₂ V₂), GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → SameGeneric O x A A' → SameGeneric O x E E' → SameGeneric O x C C' → QuotExact O x A.lat A'.lat E.lat E'.lat C.lat C'.lat → ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d N E E' k L Q = ck O x d N₀ A A' k L Q + ck O x d N₂ C C' k L Q := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x d N₀ N N₂ V₀ _ _ V _ _ V₂ _ _ A A' E E' C C' hM hA hE hC hX k hk1 hk2 q L Q hQ
  obtain ⟨E'', h1, h2, h3, h4⟩ :=
    GlobalTheory.T.chart_bundle_extension_comparison O Ω K ι x N₀ N N₂ V₀ V V₂ A.lat A'.lat E E' C C' hX
  have hEE'' : SameGeneric O x E E'' := fun s hs =>
    ⟨fun v hv => by
        obtain ⟨c, hc, hcv⟩ := (hE s hs).1 v hv
        exact ⟨c, hc, h1 s hs hcv⟩,
      fun v hv => ⟨1, one_ne_zero, by simpa using h2 s hs hv⟩⟩
  have hE''E' : SameGeneric O x E'' E' := fun s hs =>
    ⟨fun v hv => (hE s hs).1 v (h2 s hs hv),
      fun v hv => ⟨1, one_ne_zero, by simpa using h1 s hs hv⟩⟩
  have hcoc := (GlobalTheory.T.dvr_bundle_statement_a O Ω K ι x d N V E E'' E' hM hEE'' hE''E' k hk1 hk2 q L Q hQ).1
  have hAe := GlobalTheory.T.chart_bundle_intersection_symmetry O Ω K ι x d N₀ N V₀ V A A' E'' E' hM hA hE''E' h3 k hk1 hk2 q L Q hQ
  have hCe := GlobalTheory.T.chart_bundle_intersection_symmetry O Ω K ι x d N N₂ V V₂ E E'' C C' hM hEE'' hC h4 k hk1 hk2 q L Q hQ
  rw [hcoc, hAe, hCe, add_comm]

end GlobalTheory.CompanionTheory.Ar.Num.QuotAdd
