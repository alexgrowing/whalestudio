import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsJumpVIffOfExactCrystallineLatticesStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory

theorem jumps_exact_adm : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
    Formalism.MainNotions.CrystallineLiftingBounds.adm23 D HW F ∧ Formalism.MainNotions.LiftingTheory.adm23 D HW F := by
  intro D HW F
  exact ⟨fun l _ K LL => GlobalTheory.T.isJumpV_iff_of_exact_crystalline_lattices l (D.loc l) (D.locA l) (D.locT l) K LL,
    fun l _ K LL => GlobalTheory.T.isJumpV_iff_of_exact_crystalline_lattices l (D.loc l) (D.locA l) (D.locT l) K LL⟩

end GlobalTheory
