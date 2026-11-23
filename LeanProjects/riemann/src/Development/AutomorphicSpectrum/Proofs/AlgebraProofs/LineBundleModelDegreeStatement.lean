import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LineBundleModelDegree
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_bundle_model_degree : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ d : ℕ, GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles.IsModelOver O (mcIdeal O x) d → ∀ (A A' : ChartBundle O (mseg x) 1 Ω) (u u' : Ω) (a a' : K → ℤ), IsLine O x u a A.lat → IsLine O x u' a' A'.lat → ∀ f g : MRing ι O, IsVerticalDivisor (pointIdeal O x) ϖ (a - a') f g → aeval x f * u = aeval x g * u' → SameGeneric O x A A' ∧ ∀ (k : ℕ), 1 ≤ k → k ≤ d + 1 → ∀ (q : ℕ) (L : Fin q → K → ℤ) (Q : MvPolynomial (Fin q) ℤ), Q.IsHomogeneous (d + 1 - k) → ck O x d 1 A A' k L Q = ∑ μ ∈ Q.support, Q.coeff μ * pairNum (pointIdeal O x) (fun _ : Fin 1 => a) (fun _ => a') (fun _ => f) (fun _ => g) (psumExpansion 1 k) (classList L μ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.LineCk.main | exact GlobalTheory.CompanionTheory.Ar.Num.LineCk.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.LineCk.main <;> assumption)
