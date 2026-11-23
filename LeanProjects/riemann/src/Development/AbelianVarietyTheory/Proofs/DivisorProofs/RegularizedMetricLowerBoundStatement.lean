import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularizedMetricLowerBound
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InSOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialSmoothOffBoundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralCutoffLogDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPotentialPositiveOnComponents
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open CategoryTheory AlgebraicGeometry ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory GlobalTheory.ShFam GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.FlagPoly
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularized_metric_lower_bound : HessSt → CentSt → OnCore fun D O x P => ∃ C t₀ : ℝ, 0 ≤ C ∧ 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ →
    ∀ c σ (u : D.what₂.Tau → Fin O.N → ℝ), Dom u → ∀ ch : AlgChart (O.var c).str σ (O.var c).dim, ∀ y ∈ ch.e.source, ∀ ξ,
      -(C * ‖u‖ * (Real.log (Real.log (1 / t)) / Real.log (1 / t)) * P.om c σ ch y ξ) ≤
        thW (refMet x O.Φ) c σ u ch y ξ + ddcForm (P.reg c σ u t) ch y ξ := by
  first | exact @GlobalTheory.RegCurvAlg.curv_lower | exact GlobalTheory.RegCurvAlg.curv_lower | (intros; apply GlobalTheory.RegCurvAlg.curv_lower <;> assumption)
