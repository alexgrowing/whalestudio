import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.Torsor
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RowForm

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)

def IotaDictNeed : Prop :=
  ∀ s₁ s₂ : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'),
    s₁.G ≠ 0 → s₂.G ≠ 0 → s₁.generic → s₂.generic →
    s₁.lam = s₂.lam → s₁.lam' = s₂.lam' →
    IotaCompat s₁.lam (lf D (X.Fu u)) s₁.frame s₂.frame (s₂.lin * s₁.lin⁻¹) (gS D) →
      iotaOf Y.TR (Y.cs u) (Y.cs u') s₁ = iotaOf Y.TR (Y.cs u) (Y.cs u') s₂

def LiftTransNeed : Prop :=
  ∀ (s : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'))
    (y : Carrier (PD D s.lam (lf D (X.Fu u)) u')) (β : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    Formalism.L2.SG.DataInst.Elig s.toTerm → Gval (lf D (X.Fu u)) y.1 ≠ 0 →
    IsPair s.lam (lf D (X.Fu u)) s.frame y.1 β (gS D) →
    Lat.s0 s.lam (lf D (X.Fu u)) s.frame y.1 β D.R.k = 1 → IsScalar s.lam (lf D (X.Fu u)) s.frame y.1 β →
      ∃ s' : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'),
        s'.lam = s.lam ∧ s'.lam' = s.lam' ∧
        s'.toTerm = (⟨s.lam, s.mem, TermDef.mk _ _ _ y⟩ : Term D u u' (X.Fu u) (Y.what₂ u)) ∧
        IotaCompat s.lam (lf D (X.Fu u)) s.frame s'.frame (s'.lin * s.lin⁻¹) (gS D)

namespace LiftCoherence

variable {X Y u u'}

theorem liftRowCoh_rowOf_eq {s s' : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')}
    (hl : s'.lam = s.lam) (hl' : s'.lam' = s.lam')
    (hi : iotaOf Y.TR (Y.cs u) (Y.cs u') s' = iotaOf Y.TR (Y.cs u) (Y.cs u') s) :
    (Y.tO u u').rowOf s' = (Y.tO u u').rowOf s := by
  show rowOf Y.TR (Y.cs u) (Y.cs u') s' = rowOf Y.TR (Y.cs u) (Y.cs u') s
  unfold rowOf
  rw [hi]
  congr 1
  · exact Subtype.ext hl
  · congr 1
    exact Subtype.ext hl'

end LiftCoherence

open LiftCoherence

theorem liftRowCohC_of (hT : LiftTransNeed X Y u u') (hD : IotaDictNeed X Y u u') : LiftRowCohC X Y u u' := by
  intro s t hs ht hst
  obtain ⟨⟨pl, pm, y₁, y₂, hy₁, hy₂, β, hβ⟩, hp₁, hp₂, hsp⟩ := hst
  let x₁ : Carrier (PD D s.lam (lf D (X.Fu u)) u') := ⟨s.frame, s.rep.2.2.2.2⟩
  have hp₁' : (Term.mk pl pm (TermDef.mk _ _ _ y₁) : Term D u u' (X.Fu u) (Y.what₂ u)) =
      Term.mk s.lam s.mem (TermDef.mk _ _ _ x₁) := hp₁
  obtain ⟨hpl, e₁⟩ := Term.mk.inj hp₁'
  subst hpl
  have hRL : IsRowLat D (X.Fu u) s.lam := (Y.rowsOK u).1 s.lam s.mem
  have hEq := Formalism.L2.SG.Closed.TermEqIff_holds D u u' (X.Fu u) s.lam hRL
  have hGF := (Formalism.L2.SG.Closed.TermFun_holds D u u' (X.Fu u) s.lam hRL).1
  have gv : ∀ x : Carrier (PD D s.lam (lf D (X.Fu u)) u'),
      Gt s.lam (lf D (X.Fu u)) (PD D s.lam (lf D (X.Fu u)) u') (TermDef.mk _ _ _ x) = Gval (lf D (X.Fu u)) x.1 := by
    intro x
    exact hGF _ _ ((hEq _ _).1 (Quot.out_eq (TermDef.mk s.lam (lf D (X.Fu u)) (PD D s.lam (lf D (X.Fu u)) u') x)))
  have hx₁ : Gval (lf D (X.Fu u)) x₁.1 ≠ 0 := by
    rw [← gv]
    exact hs.2
  have r₁ := (hEq y₁ x₁).1 (eq_of_heq e₁)
  have hSE := Formalism.L2.SG.Closed.ScalarEquiv_holds D u u' (X.Fu u) s.lam hRL
  have hRF := Formalism.L2.SG.Closed.ScalarRepFree_holds D u u' (X.Fu u) s.lam hRL
  have a1 : Formalism.L2.SG.Corank.ScalRelD D u' (X.Fu u) s.lam ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩ := ⟨β, hβ, hsp.1, hsp.2⟩
  have a2 := hRF ⟨y₂, hy₂⟩ ⟨y₁, hy₁⟩ ⟨x₁, hx₁⟩ r₁ (hSE.symm a1)
  obtain ⟨β', hβ', h1, h2⟩ := hSE.symm a2
  obtain ⟨s', hl, hl', hs't, hic⟩ := hT s y₂ β' hs hy₂ hβ' h1 h2
  have hs't' : s'.toTerm = t := hs't.trans hp₂
  refine ⟨s', hs't', ?_⟩
  have hE' : Formalism.L2.SG.DataInst.Elig s'.toTerm := hs't' ▸ ht
  have hi := hD s s' hs.2 hE'.2 hs.1 hE'.1 hl.symm hl'.symm hic
  exact liftRowCoh_rowOf_eq hl hl' hi.symm

end Formalism.L2.SG.Pf.RowForm
