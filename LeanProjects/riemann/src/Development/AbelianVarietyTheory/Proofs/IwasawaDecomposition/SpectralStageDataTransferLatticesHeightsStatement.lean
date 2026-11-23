import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpectralStageDataTransferLatticesHeights
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spectralStageData_transfer_lattices_heights : GlobalTheory.Mem.SRe.SxMv := by
  first | exact @GlobalTheory.Mem.SRe.SxPass.sxMv | exact GlobalTheory.Mem.SRe.SxPass.sxMv | (intros; apply GlobalTheory.Mem.SRe.SxPass.sxMv <;> assumption)
