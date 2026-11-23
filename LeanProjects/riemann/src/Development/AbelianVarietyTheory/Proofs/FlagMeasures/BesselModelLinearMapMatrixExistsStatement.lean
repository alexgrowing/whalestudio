import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelLinearMapMatrixExists
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointGramMinorsAgreeProof
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Choice
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopTermLem
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselModel_linearMap_matrix_exists : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (τ : D.what₂.Tau) (m : (VS D).V →ₗ[D.host.E] (VS D).V),
    ∃ n : MatKR D.R.k D.R.rS, ∀ y, n *ᵥ GlobalTheory.TypeAsm.phiV C τ y = GlobalTheory.TypeAsm.phiV C τ (m y) := by
  first | exact @GlobalTheory.TypeAsm.phiV_linMat_all | exact GlobalTheory.TypeAsm.phiV_linMat_all | (intros; apply GlobalTheory.TypeAsm.phiV_linMat_all <;> assumption)
