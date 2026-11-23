import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.FlagMinor
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.PluckerCoord
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ModelPushforwardFibreDegree
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.field_extension_intersection_invariance : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ d : ℕ, IsModelOver (pointIdeal O x) d → ∀ (Ω₁ : Type) [Field Ω₁] [Algebra O Ω₁] [Algebra Ω Ω₁] [IsScalarTower O Ω Ω₁] (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω₁), IsModelOver (pointIdeal O (bcCoord x z)) d → ∀ (c : K → ℕ) (f : MRing ι O), IsMultiHomog f c → f ∉ (pointIdeal O x) → ∀ l : List (K → ℤ), l.length = d → (open Classical in cycEval (fun W => if (C ϖ : MRing (Sum.elim ι ι') O) ∈ W then vNumL W (l.map (pullDeg (K' := K'))) else 0) (divCycle (pointIdeal O (bcCoord x z)) (rename (liftVar ι') f))) = (modelDeg O x z : ℤ) * (open Classical in cycEval (fun W => if (C ϖ : MRing ι O) ∈ W then vNumL W l else 0) (divCycle (pointIdeal O x) f)) := by
  first | exact @PositivityTheory.Xgn.model_pushforward_fibre_degree | exact PositivityTheory.Xgn.model_pushforward_fibre_degree
