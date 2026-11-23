import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TransferStatementBis
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.InhabitedFinite
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.TransferStatementBis : StTransfer := by
  first | exact @GlobalTheory.CompanionTheory.HeckeTransfer.stTransfer | exact GlobalTheory.CompanionTheory.HeckeTransfer.stTransfer | (intros; apply GlobalTheory.CompanionTheory.HeckeTransfer.stTransfer <;> assumption)
