import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralConjugationSymmetry
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPieceDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.points_integral_conjugation_symmetry : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (Ψ Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (L : Fin e → HermLine ι) (B B' : HermLine ι), IsArithVar P (e + 1) → IsGoodProj P Ψ → (∀ w, Ψ' (star w) = star (Ψ w)) → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsConjInvariantH (L j)) → B.a = 0 → IsSmoothHerm B → B'.a = 0 → IsSmoothHerm B' → (∀ z ∈ mcPts P, B'.h (star z) = B.h z) → IsGoodProj P Ψ' ∧ ptsIntegralAt P Ψ' (pot L) (logNorm B' 1) = ptsIntegralAt P Ψ (pot L) (logNorm B 1) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegralAt_conj | exact GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegralAt_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegralAt_conj <;> assumption)
