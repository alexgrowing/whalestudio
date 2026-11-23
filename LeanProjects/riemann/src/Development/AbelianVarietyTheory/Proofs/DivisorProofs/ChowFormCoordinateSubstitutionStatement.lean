import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormCoordinateSubstitution
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
theorem _root_.GlobalTheory.T.chow_form_coordinate_substitution : ∀ (K : Type) [Field K] (N n D δ : ℕ) (I : Ideal (MvPolynomial (Fin N) K)) (I' : Ideal (MvPolynomial (Fin n) K)) (f : MvPolynomial (Fin (D + 1) × Fin N) K), N ≤ n →
    (∀ q, q ∈ I' ↔ GlobalTheory.CompHt.coordSubst (Matrix.of fun (j : Fin N) (k : Fin n) => if (j : ℕ) = (k : ℕ) then (1 : K) else 0) q ∈ I) → GlobalTheory.ChowHt.IsChowFormInt I D δ f →
    GlobalTheory.ChowHt.IsChowFormInt I' D δ (GlobalTheory.ChowHt.linSubst (Matrix.of fun (j : Fin N) (k : Fin n) => if (j : ℕ) = (k : ℕ) then (1 : K) else 0) f) := by
  first | exact @GlobalTheory.ChowIncl.isChowFormInt_incl | exact GlobalTheory.ChowIncl.isChowFormInt_incl | (intros; apply GlobalTheory.ChowIncl.isChowFormInt_incl <;> assumption)
