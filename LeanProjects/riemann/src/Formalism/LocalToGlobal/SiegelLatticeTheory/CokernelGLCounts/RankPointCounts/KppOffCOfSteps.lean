import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KappaOffDiagonal
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TermAttrConst

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {α : Type*} {r : α → α → Prop}

theorem eqvGen_iff_of (f : α → Prop) (hf : ∀ a b, r a b → (f a ↔ f b)) {a b : α} (h : Relation.EqvGen r a b) :
    (f a ↔ f b) := by
  induction h with
  | rel x y hxy => exact hf x y hxy
  | refl x => exact Iff.rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

theorem eqvGen_eq_of {β : Type*} (f : α → β) (hf : ∀ a b, r a b → f a = f b) {a b : α} (h : Relation.EqvGen r a b) :
    f a = f b := by
  induction h with
  | rel x y hxy => exact hf x y hxy
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2

end Gen

theorem relRepC : RelRepC := by
  intro D X Y u u' t hr hG
  have hΛ : IsRowLat D (X.Fu u) t.lam := (Y.rowsOK u).1 t.lam t.mem
  obtain ⟨hGF, -, hRF, -, -⟩ := term_function_const D u u' (X.Fu u) t.lam hΛ

  set x : TermDef.Carrier (TermDef.PD D t.lam (lf D (X.Fu u)) u') := ⟨frq X t.rep, t.rep.2.2.2.2⟩ with hx
  have hcls : t.toTerm.cls = TermDef.mk t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u') x := rfl
  constructor
  · obtain ⟨F', ⟨hP, hmk⟩, hrel⟩ := hr
    have hcls' : t.toTerm.cls = TermDef.mk t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u') x := hcls
    rw [hcls'] at hmk
    have he : Relation.EqvGen (TermDef.Rel t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u')) ⟨F', hP⟩ x :=
      Quot.eqvGen_exact hmk
    exact (eqvGen_iff_of (fun y : TermDef.Carrier (TermDef.PD D t.lam (lf D (X.Fu u)) u') =>
      Relevant D.host.F (lf D (X.Fu u)).fl y.1.fl) (fun a b hab => hRF a b hab) he).1 hrel
  · have hG' : TermDef.Gt t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u')
        (TermDef.mk t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u') x) = 0 := hG
    unfold TermDef.Gt at hG'
    have hout := Quot.out_eq (TermDef.mk t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u') x)
    have he : Relation.EqvGen (TermDef.Rel t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u'))
        (Quot.out (TermDef.mk t.lam (lf D (X.Fu u)) (TermDef.PD D t.lam (lf D (X.Fu u)) u') x)) x :=
      Quot.eqvGen_exact hout
    have := eqvGen_eq_of (fun y : TermDef.Carrier (TermDef.PD D t.lam (lf D (X.Fu u)) u') =>
      Gval (lf D (X.Fu u)) y.1) (fun a b hab => hGF a b hab) he
    rw [← this]; exact hG'

theorem kppOffC_of_steps (hFold : FoldOKC) (hFE : FundExistsC) (hOI : OOIntAllC) (hV : LemmaVC)
    (hCov : CovRepC) (hSch : SchurNFC) : Formalism.L2.SG.RowsConc.KppOffC :=
  kppOffC_of_cut hFold hFE hOI hV relRepC hCov hSch

end Formalism.L2.SG.KappaOffDiagonal
