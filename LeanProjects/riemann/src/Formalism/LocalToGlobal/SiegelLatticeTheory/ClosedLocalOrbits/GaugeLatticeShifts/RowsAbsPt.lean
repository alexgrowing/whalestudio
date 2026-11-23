import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RowsAbsX
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PtCellUniq
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermDef

namespace Formalism.L2.SG.RowsAbsX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem atPt_uniq {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}
    (Λ : Submodule (𝓞 E) S.V) {T T' : E} (F : LFlag S r T) (P : LFlag S r T' → Prop) (t : TermQ Λ F P)
    (w w' : Point E (r + 1)) (h : AtPt Λ F P t w) (h' : AtPt Λ F P t w') : w = w' := by
  obtain ⟨F₁, ⟨h₁, e₁⟩, -, c₁⟩ := h
  obtain ⟨F₂, ⟨h₂, e₂⟩, -, c₂⟩ := h'
  have hq : Quot.mk (Rel Λ F P) ⟨F₁, h₁⟩ = Quot.mk (Rel Λ F P) ⟨F₂, h₂⟩ := e₁.trans e₂.symm
  have hg := Quot.eqvGen_exact hq
  have inv : ∀ x y : Carrier P, Relation.EqvGen (Rel Λ F P) x y → ∀ v : Point E (r + 1),
      (IsInCell (ZhatOM (ZhatL F x.1)) v ↔ IsInCell (ZhatOM (ZhatL F y.1)) v) := by
    intro x y hxy
    induction hxy with
    | rel x y hr => exact Formalism.L2.SG.Pf.cell_function_holds Λ F P x y hr
    | refl x => exact fun v => Iff.rfl
    | symm x y _ ih => exact fun v => (ih v).symm
    | trans x y z _ _ ih₁ ih₂ => exact fun v => (ih₁ v).trans (ih₂ v)
  exact Formalism.L2.SG.PtCell.isInCell_uniq ((inv _ _ hg w).1 c₁) c₂

variable {D : D7} (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)

theorem ptUniq_holds : PtUniq X Y u u' := fun t w w' h h' => atPt_uniq _ _ _ t.cls w w' h h'

end Formalism.L2.SG.RowsAbsX
