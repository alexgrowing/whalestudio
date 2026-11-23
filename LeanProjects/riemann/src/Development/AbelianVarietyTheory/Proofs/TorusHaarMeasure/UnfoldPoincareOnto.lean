import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustGPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.RhGradFPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OmFConnPf
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasureStatements
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OneLeMinorOfIsOrth
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MulSgnMatMulConjTranspose
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IsUpqSubmatrix
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsLeNormDev
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormFderivLeOfClosedBallSubset
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.KaFrameOfDelta
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.KaUnfoldOfUnfoldOfKappa
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormBcharMulNfacRmul
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.DminCptEq
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.PairUnfoldOfUnfold
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.PoinStatementOf
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.PoinSummableIsBddSec
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.OfRealTsumSqLeTsumDivMulTsum
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.LintegralLeDensity
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormLeSqrtWeightNearOrthonormal
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurableSetSatFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IntegralEqIntegralTsumOfLintegral

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

namespace GlobalTheory.PoincareClosed

theorem unfold_poincare_onto :
    (∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → ∀ FF, IsFundSet X x0 FF → ∀ ψ : Frame X.Ψ r → ℝ≥0∞, Measurable ψ → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul x b) = ψ x) → ∫⁻ z, ψ (cpt X x0 z) ∂muF X x0 = ∫⁻ z in FF, ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z)) ∂muF X x0) ∧ (KaUnfoldStatement (E := E)) ∧ (PairUnfoldStatement (E := E)) ∧ (PoinStatement (E := E)) ∧ (OntoStatement (E := E)) := by
  obtain ⟨-, hMeas, -, hExt⟩ := GlobalTheory.FrameMeasureClosed.measure_statements (E := E)
  have hUnf := GlobalTheory.Unfold.lintegral_unfold (E := E) hMeas
  have hκ := GlobalTheory.kaFrame (E := E) GlobalTheory.FramePotential.frame_potential_basic
    GlobalTheory.MinorRatioNear.minorRatio_near (GlobalTheory.FrameSumBound.frame_sum_bound GlobalTheory.grpSep)
  have hKa : KaUnfoldStatement (E := E) := GlobalTheory.kaUnfold_of_unfold_of_kappa hUnf hκ
  have hPair : PairUnfoldStatement (E := E) :=
    GlobalTheory.PairUnfold.pairUnfold_of_unfold (GlobalTheory.UnfoldComplex.unfold_integral hUnf) hKa
  have hN := GlobalTheory.NormFactor.nfac_transform (E := E)
  have hPoin : PoinStatement (E := E) :=
    GlobalTheory.PoincareAssembly.poinStatement_of hκ
      (GlobalTheory.PointSup.pointSup hMeas GlobalTheory.OrthNear.orthNear hN)
      (GlobalTheory.norm_le_sqrt_weight_near_orthonormal hMeas GlobalTheory.OrthNear.orthNear hN)
      (GlobalTheory.PoinHol.poin_summable_isBddSec GlobalTheory.differentiableOn_tsum_of_norm_le hN)
      (GlobalTheory.poincare_sqIntegrable_fundSet hUnf)
  exact ⟨hUnf, hKa, hPair, hPoin,
    onto_of hPoin hExt RhGradFStatement_holds exhaustG_holds hKa hPair bigCellStatement_holds
      OmFConnStatement_holds⟩

end GlobalTheory.PoincareClosed
