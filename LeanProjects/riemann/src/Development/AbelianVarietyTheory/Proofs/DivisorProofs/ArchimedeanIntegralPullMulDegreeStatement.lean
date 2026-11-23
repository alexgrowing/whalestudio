import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanIntegralPullMulDegree
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanIntegral_pull_mul_degree : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (e : ℕ), IsArithVar p e → IsArithVar q e → ∀ (g : Y ⟶ X) (hg : g ≫ p = q) (hη : g (genericPoint Y) = genericPoint X), g.residueDegree (genericPoint Y) ≠ 0 → ∀ (M N : HermLB p) (r : M.B.ι → X.functionFieldˣ) (hr : IsRatSec M.B r), (N.pull g hg).archInt (M.pull g hg) e (MultPull.isRatSec_pull_map g (hη ▸ specializes_rfl : g (genericPoint Y) ⤳ genericPoint X) hr) = (g.residueDegree (genericPoint Y) : ℝ) * N.archInt M e hr := by
  first | exact @GlobalTheory.ArchPull.archInt_pull | exact GlobalTheory.ArchPull.archInt_pull | (intros; apply GlobalTheory.ArchPull.archInt_pull <;> assumption)
