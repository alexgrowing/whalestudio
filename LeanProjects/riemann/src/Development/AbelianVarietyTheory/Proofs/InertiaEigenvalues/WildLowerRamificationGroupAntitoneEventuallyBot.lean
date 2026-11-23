import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoTowerQ

open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem wild_antitone_and_eventually_bot :
    ∀ (K L : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsGalois K L], Antitone (wild K L) ∧ ∃ m, wild K L m = ⊥ := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _
  refine ⟨fun i j hij ↦ ?_, ?_⟩
  · exact lowerRamificationGroup_antitone K L (by simp only [add_le_add_iff_right, Nat.cast_le]; exact hij)
  · obtain ⟨n, hn⟩ := exists_lowerRamificationGroup_eq_bot K L
    exact ⟨n, hn _ (by omega)⟩

end GlobalTheory.PMon.Ram
