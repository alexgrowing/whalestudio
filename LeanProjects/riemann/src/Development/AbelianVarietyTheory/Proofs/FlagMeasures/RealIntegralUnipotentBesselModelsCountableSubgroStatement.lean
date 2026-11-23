import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealIntegralUnipotentBesselModelsCountableSubgro
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
open scoped Classical ENNReal Pointwise NNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realIntegralUnipotent_besselModels_countable_subgroup : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word) (C : Choice X 1),
    (trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u).Countable ∧
    (fun _ => Matrix.of.symm 1) ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u ∧
    (∀ m ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u, ∀ m' ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u,
      GlobalTheory.DegVol.mulP m m' ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) ∧
    (∀ m ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u,
      (fun τ => Matrix.of.symm (Matrix.of (m τ))⁻¹) ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) ∧
    ∀ m ∈ trI C '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u, ∀ τ, Matrix.of (m τ) ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS := by
  first | exact @GlobalTheory.CovGrp.cov_grp | exact GlobalTheory.CovGrp.cov_grp | (intros; apply GlobalTheory.CovGrp.cov_grp <;> assumption)
