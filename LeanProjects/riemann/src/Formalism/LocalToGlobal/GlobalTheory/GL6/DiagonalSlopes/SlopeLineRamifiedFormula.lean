import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.SlopeFormulaOfCharacterFinite
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.CharacterFiniteLevelZeroOfForms
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.GroupActionMulSingleEqDilation
import Formalism.SharpRestriction.GlobalSchurBounds.FiniteModelOfAdmissibleTransports
import Formalism.LocalToGlobal.GlobalTheory.GL6.DiagonalSlopes.AdmissibleStabilisersOfCompatibleForms
import Formalism.SharpRestriction.GlobalSchurBounds.LinkMin

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

open Formalism.BasicNotions Formalism.L2.Forms Classical

section Model

variable {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} {C : ColumnChain R ι hc}

theorem rank_model_mulSingle (A : ColumnsAtT R C) (M : FreeRankModel A) (v : A.vT) (a : (A.Fv v)ˣ) :
    (MulEquiv.piCongrRight M.e) (Pi.mulSingle v a : ∀ v : A.vT, (A.Fv v)ˣ) = (Pi.mulSingle v (M.e v a) : A.vT → M.H) := by
  funext w
  rw [MulEquiv.piCongrRight_apply]
  by_cases h : w = v
  · subst h
    simp only [Pi.mulSingle_eq_same]
  · simp only [Pi.mulSingle_eq_of_ne h, map_one]

end Model

variable {D : D7} {u : D.what₂.Word}

def freeT_of_model (M : FreeRankModel (D.mem u).A) : Formalism.MainNotions.product_first_zeroth_parts.FreeT D u :=
  letI : MulAction (∀ v : (D.mem u).A.vT, ((D.mem u).A.Fv v)ˣ) M.X :=
    MulAction.compHom M.X (MulEquiv.piCongrRight M.e).toMonoidHom
  { X := M.X
    free := fun g x h => by
      have h1 : (MulEquiv.piCongrRight M.e) g = 1 := M.free _ x h
      exact (MulEquiv.map_eq_one_iff _).1 h1
    Θ := M.E
    equiv := fun v a φ h x => by
      rw [M.intertw v a φ h x]
      show M.E φ _ = M.E φ ((MulEquiv.piCongrRight M.e).toMonoidHom (Pi.mulSingle v a) • x)
      rw [MulEquiv.coe_toMonoidHom, rank_model_mulSingle] }

theorem freeT_of_tied (Tf : Forms0 D u) (hS : Formalism.MainNotions.product_first_zeroth_parts.admS D u) : Nonempty (Formalism.MainNotions.product_first_zeroth_parts.FreeT D u) := by
  exact ⟨freeT_of_model (free_rank_model_of_split Tf hS (splitAtT_of_tied Tf.atT)).some⟩

theorem slopeLine_iff_ramifiedSlopeFormula : Formalism.MainNotions.product_first_zeroth_parts.SlopeLine D u ↔ RamifiedSlopeFormula D u := Iff.rfl

theorem slopeLine_of_tied (hS : Formalism.MainNotions.product_first_zeroth_parts.HidaSetting D u) (Tf : Forms0 D u) (hC : ChiFin0 Tf)
    (hA : Formalism.MainNotions.product_first_zeroth_parts.admS D u) : Formalism.MainNotions.product_first_zeroth_parts.SlopeLine D u := by
  exact slopeLine_iff_ramifiedSlopeFormula.2 (slope_formula_of_character_finite hS Tf hC hA)

theorem freeT_tied (Tf : Forms0 D u) : Nonempty (Formalism.MainNotions.product_first_zeroth_parts.FreeT D u) := by
  exact freeT_of_tied Tf (admissible_stabilisers_of_compatible_forms Tf)

theorem slopeLine_tied (hS : Formalism.MainNotions.product_first_zeroth_parts.HidaSetting D u) (Tf : Forms0 D u) (hC : ChiFin0 Tf) : Formalism.MainNotions.product_first_zeroth_parts.SlopeLine D u := by
  exact slopeLine_of_tied hS Tf hC (admissible_stabilisers_of_compatible_forms Tf)

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.L2.Forms

variable {D : D7} {u : D.what₂.Word}

theorem freeT_0 (T : Forms0 D u) : Nonempty (Formalism.MainNotions.product_first_zeroth_parts.FreeT D u) := S0.freeT_tied T

theorem slopeLine_0 (hS : Formalism.MainNotions.product_first_zeroth_parts.HidaSetting D u) (T : Forms0 D u) (hC : ChiFin0 T) : Formalism.MainNotions.product_first_zeroth_parts.SlopeLine D u := S0.slopeLine_tied hS T hC

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
