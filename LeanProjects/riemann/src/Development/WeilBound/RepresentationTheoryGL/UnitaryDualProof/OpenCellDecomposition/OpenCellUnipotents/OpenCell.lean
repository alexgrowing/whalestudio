import Mathlib
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.OpenCellDecomposition.OpenCellUnipotents.ValuationLeOneOfNabsLt

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.Rodier GlobalTheory.SplitWeil GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.CellA

set_option maxHeartbeats 2000000 in

theorem openCell (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PositivityTheory.RgUd.OpenCell k := by
  intro ψ hψ _ r m V W _ _ _ _ A x ω hA hx hgA hgx hxω z hz
  obtain ⟨φ⟩ := bridge_equiv (k := k) A x
  have hs : ∀ a, IsSmooth (piPair A x a) := fun a => by
    fin_cases a
    · exact hA
    · exact hx
  obtain ⟨F, hF, hi⟩ := openCellPar ψ hψ (piTensor (piPair A x)) (isSmooth_piTensor hs) ω
    (piPair_levZ A x ω hxω) (exists_not_mem_twKer ψ A x hgA hgx) z hz
  have e : φ (φ.symm F) = F := by
    first
      | exact φ.apply_symm_apply F
      | exact φ.toLinearEquiv.apply_symm_apply F
      | simp
  refine ⟨φ.symm F, φ.symm F, fun hmem => hF ?_, 0, fun i _ => ?_⟩
  · have := (equiv_mem_twKer φ _ _ (φ.symm F)).2 hmem
    rw [e] at this
    exact this
  · rw [← equiv_mem_twKer φ, map_sub, map_smul, equiv_apply, e]
    exact hi i

end PositivityTheory.RgUd.CellA
