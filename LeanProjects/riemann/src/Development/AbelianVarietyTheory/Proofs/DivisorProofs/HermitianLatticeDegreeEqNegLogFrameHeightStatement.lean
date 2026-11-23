import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeDegreeEqNegLogFrameHeight
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Formalism.HarderNarasimhan.StatementPl
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_lattice_degree_eq_neg_log_frame_height : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [StarRing K] [IsTotallyComplex K] [FiniteDimensional K V] (nm : HermFam K V), nm.IsConjInv → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) → (∀ v x, Formalism.HermitianLatticesTheory.normAt b X v x = nm.nrm v.embedding x) → ∀ L : Submodule (𝓞 K) V, L.FG → deg nm L = -Real.log (Formalism.HN.ht b X L) / (2 * (Formalism.HN.nPl K : ℝ)) := by
  first | exact @GlobalTheory.FrameDeg.deg_eq_neg_log_ht | exact GlobalTheory.FrameDeg.deg_eq_neg_log_ht | (intros; apply GlobalTheory.FrameDeg.deg_eq_neg_log_ht <;> assumption)
