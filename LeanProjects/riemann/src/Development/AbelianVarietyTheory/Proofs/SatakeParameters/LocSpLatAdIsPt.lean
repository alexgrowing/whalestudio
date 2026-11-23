import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FacQIsPt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaSeriesDataHypothesesBelowMaximalLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.MovDXiAtRecStep
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.LocalClassDataOfTrivialStabilizers
import Formalism.LocalToGlobal.GlobalTheory.BaseLatticeSelfDual
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.SpanPt

theorem colSpan_map {R K : Type*} [CommRing R] [Field K] [Algebra R K] {k : ℕ} (M X : Matrix (Fin k) (Fin k) K) :
    (colSpan R X).map ((M.mulVecLin).restrictScalars R) = colSpan R (M * X) := by
  unfold colSpan
  rw [Submodule.map_span, ← Set.range_comp]
  congr 1

set_option maxHeartbeats 400000 in

theorem locSp_latAd_isPt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p} (A : LocAt F E n G) (Lb : Submodule (𝓞 E) (Fin n → E)), LatAdLoc A Lb → LbAtB A Lb → ∀ (i : G.comp) (g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v)) (y : GL (Fin n) (E ⊗[F] (FiniteAdeleRing (𝓞 F) F))), A.IsPt i g y → ∀ v, locSp (G.P.W v) (A.iw v) (latAd y Lb) = colSpan (G.P.W v) (((bc (A.iw v) A.B : GL (Fin n) (G.P.Qq v)) : Matrix (Fin n) (Fin n) (G.P.Qq v)) * (castGL A.rk (G.P.Qq v) (g v) : Matrix (Fin n) (Fin n) (G.P.Qq v))) := by
  intro F E _ _ _ _ _ n p G A Lb hA hB i g y hy v
  rw [hA y v, hB v, colSpan_map, GlobalTheory.TwV.FacQPt.facQ_isPt A i g y hy v]
  simp only [Units.val_mul, Matrix.mul_assoc]
  rw [← Units.val_mul (bc (A.iw v) A.B)⁻¹, inv_mul_cancel, Units.val_one, Matrix.mul_one]

end GlobalTheory.TwV.SpanPt

end
