import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FrameOfAnisotropicPlaneSplitting
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_of_anisotropic_plane_splitting : StAniso → StPlane → StSplit → StFrame := by
  first | exact @GlobalTheory.CompanionTheory.HermFrame.stFrame_of | exact GlobalTheory.CompanionTheory.HermFrame.stFrame_of | (intros; apply GlobalTheory.CompanionTheory.HermFrame.stFrame_of <;> assumption)
