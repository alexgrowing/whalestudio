import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.AdelicU Formalism.UG

namespace GlobalTheory.IsoColReal

theorem compInf_incA {D : D7} (w : InfinitePlace D.host.F) (x : D.host.E) :
    compInf D.host.F D.host.E w (incA D x) = inclR (F := D.host.F) w.Completion x := by
  simp [compInf, incA, inclR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]

theorem sigR_inclR_real {D : D7} (w : InfinitePlace D.host.F) (x : D.host.E) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion D.sp.cm.sig (inclR (F := D.host.F) w.Completion x) = inclR (F := D.host.F) w.Completion (star x) := by
  simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, inclR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]
  rfl

theorem isotropic_at_real : ∀ {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (w : InfinitePlace D.host.F), (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion D.sp.cm.sig) (Matrix.map d.jX (compInf D.host.F D.host.E w)) * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR w.Completion T.gram : Matrix (Fin r) (Fin T.rank) (TensorProduct D.host.F w.Completion D.host.E)) * Matrix.map d.jX (compInf D.host.F D.host.E w) = 0 := by
  intro D T T₀ r d w
  have hm : Matrix.map d.jX (compInf D.host.F D.host.E w) = d.e.map (inclR (F := D.host.F) w.Completion) := by
    ext i j
    simp [HypDec.jX, rat, compInf_incA]
  have hc : Formalism.UG.cT (sigR w.Completion D.sp.cm.sig) (d.e.map (inclR (F := D.host.F) w.Completion)) =
      (d.eᴴ).map (inclR (F := D.host.F) w.Completion) := by
    ext i j
    simp [Formalism.UG.cT, Matrix.conjTranspose_apply, sigR_inclR_real]
  have hJ : JR w.Completion T.gram = T.gram.map (inclR (F := D.host.F) w.Completion) := rfl
  rw [hm, hc, hJ]
  have h0 := congrArg (fun M => M.map (inclR (F := D.host.F) w.Completion)) d.ee
  simp only [Matrix.map_mul, Matrix.map_zero, map_zero] at h0
  exact h0

end GlobalTheory.IsoColReal
