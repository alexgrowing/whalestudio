import Mathlib
import Formalism.LocalToGlobal.ThresholdSelection
import Formalism.SharpRestriction.GlobalSchurBounds.MassRatioUnfoldedOfTheoremTwo
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeFamilyOfFormalDegreeInput
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExactRanksAlongTiedFamily
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TFrameOfRanksRowThree
open Formalism.BasicNotions Formalism.MainNotions

namespace GlobalTheory

theorem ranks_and_frame_of_tied_class : (∀ D : D7, RT.MassRatioUnderVolume D) → ∀ (𝒞 : FamClass), Formalism.L2.TSel 𝒞 →
    (Closed 𝒞 fun Fm _ => PX.RanksF Fm 3 (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu) ∧
      Closed 𝒞 fun Fm _ => PX.TFrame Fm (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu 3 := by
  intro hU 𝒞 sel
  have hR : Closed 𝒞 fun Fm _ => PX.RanksF Fm 3 (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu :=
    Formalism.MainNotions.Pk.Closed.of_class fun Fm _ hc =>
      exact_ranks_along_tied_family hU _ Fm (sel Fm hc) _ _ _ _ _ _
  exact ⟨hR, GlobalTheory.tFrame_of_ranksRow_three 𝒞 hR⟩

end GlobalTheory
