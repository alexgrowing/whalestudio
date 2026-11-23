import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RowsPtAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LoopEvaluationThresholdZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DegenerateConstant
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTerm
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf GlobalTheory.Core.Deg
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.Core.Deg

theorem vanishingGramBound_uniformWindow_and_weightData : (VanishingGramTermsBoundWindow → ∀ c : ℝ, On {c} VanishingGramTermsBound) ∧ (VanishingGramTermsBoundParams → Led1 VanishingGramTermsBound) := by
  refine ⟨fun h c => ?_, fun h => ?_⟩
  · intro Cg cb Cu cT CT h1 h2
    obtain ⟨a, b, H⟩ := h Cg cb Cu cT CT c h1 h2
    refine ⟨max a b, fun C0 hC0 C' Cl hC' hCl D large₂ X Y hF hI u _ t r s d e => ?_⟩
    rw [Set.mem_singleton_iff] at hC0
    subst hC0
    exact H C' Cl (le_trans (le_max_left _ _) hC') (le_trans (le_max_right _ _) hCl) D large₂ X Y hF hI u t r s d e
  · intro Cg cb Cu cT CT h1 h2
    obtain ⟨a, b, H⟩ := h Cg cb Cu cT CT h1 h2
    exact ⟨max a b, fun C' Cl hC' hCl D large₂ X Y hF hI u _ t r s n d e =>
      H C' Cl (le_trans (le_max_left _ _) hC') (le_trans (le_max_right _ _) hCl) D large₂ X Y hF hI u t r s n d e⟩

end GlobalTheory.Core.Deg
