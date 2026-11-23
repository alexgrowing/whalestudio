import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveChartSurjectiveFunction
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FsSumPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfInterShiftLeOfBase
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FubiniStudyChowHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMultiHomogeneousRenameCastLE
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KrullDimOneOfFiniteGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameConjugateEmbeddingEqConjMulUnitary
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
open NumberField CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.ChowHt GlobalTheory.CompHt
open scoped Classical
attribute [local instance] MvPolynomial.gradedAlgebra

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_chart_surjective_function : ∀ (K Ω : Type) [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (m : ℕ) (z : Fin (m + 1) → Ω) (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (π : X ⟶ PSpace (𝓞 K) m) (ψ : Ω →+* X.functionField) (i : Fin (m + 1)) (U : X.Opens) (hη : genericPoint X ∈ U) (hU : U ≤ π ⁻¹ᵁ GlobalTheory.ProjSpace.chart (𝓞 K) m i),
    π ≫ PSpace.str (𝓞 K) m = p → Function.Surjective ψ →
    (∀ a : 𝓞 K, ψ (algebraMap K Ω (a : K)) = fnOf ⊤ (TopologicalSpace.Opens.mem_top _) (algX p ⊤ a)) →
    IntermediateField.adjoin K (Set.range z) = ⊤ → (∀ j, fnOf U hη (GlobalTheory.ProjSpace.pullRatio π U i hU j) = ψ (z j)) →
    π.residueDegree (genericPoint X) = 1 := by
  first | exact @GlobalTheory.ResDegRatio.residueDegree_eq_one_of_ratios | exact GlobalTheory.ResDegRatio.residueDegree_eq_one_of_ratios | (intros; apply GlobalTheory.ResDegRatio.residueDegree_eq_one_of_ratios <;> assumption)
