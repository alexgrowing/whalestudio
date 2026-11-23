import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RowsConc

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full

namespace Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : D7} (X : HidaSetting D) {u u' : D.what₂.Word} {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V}

def frq (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ') : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E) :=
  mapLF q.1.2 (lf D (X.Fu u'))

def fixedSubspaceOfRepresentative (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ') : Submodule D.host.E (VS D).V :=
  (lf D (X.Fu u)).fl.Xplus ⊔ (frq X q).fl.Xplus

def pointwiseStabilizerInfinite (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ') : Set X.B.I.Ginf :=
  Hset X.B.I (X.crd '' (fixedSubspaceOfRepresentative X q : Set (VS D).V))

end Defs

def RelRepC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')),
    t.relevant → t.G = 0 →
    Relevant D.host.F (lf D (X.Fu u)).fl (frq X t.rep).fl ∧ Gval (lf D (X.Fu u)) (frq X t.rep) = 0

def CovRepC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V)
    (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ'),
    Relevant D.host.F (lf D (X.Fu u)).fl (frq X q).fl →
    ∀ Ω : Set X.B.I.Ginf, IsSFund X.B.I (ROset X (X.Fu u) (X.Fu u') Λ Λ' q.1.2) Ω →
    OOInt (Formalism.L2.SG.ProjRows.muInf X.B.I) Ω (X.Wu u) (X.Wu u') q.1.1.1 →
    ∀ h ∈ pointwiseStabilizerInfinite X q,
      (haveI := FiniteDimensional.complete ℂ (X.Vpi u)
       (X.piU u h).comp (OO (Formalism.L2.SG.ProjRows.muInf X.B.I) Ω (X.Wu u) (X.Wu u') q.1.1.1) =
        (OO (Formalism.L2.SG.ProjRows.muInf X.B.I) Ω (X.Wu u) (X.Wu u') q.1.1.1).comp
          (X.piU u' (q.1.1.1⁻¹ * h * q.1.1.1)))

def SchurNFC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V)
    (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ'),
    (∀ τ, uS D u τ ≠ uS D u' τ) →
    Relevant D.host.F (lf D (X.Fu u)).fl (frq X q).fl → Gval (lf D (X.Fu u)) (frq X q) = 0 →
    ∀ P : X.Vpi u' →L[ℂ] X.Vpi u,
      (∀ h ∈ pointwiseStabilizerInfinite X q, (X.piU u h).comp P = P.comp (X.piU u' (q.1.1.1⁻¹ * h * q.1.1.1))) → P = 0

section Asm

variable {D : D7} {X : HidaSetting D}

theorem words_differ {large₂ : SizeData₂ D} {C' Cl Cg cb Cw cT CT C0 : ℝ}
    (h : Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0) {u u' : D.what₂.Word} (huu : u ≠ u') :
    ∀ τ, uS D u τ ≠ uS D u' τ := by
  exact h.1.2.1.2.2.2.2.2.2.2.1 u u' huu

theorem aTerm_eq_zero_of_OOt {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (cs : ColSys X u what₂) (cs' : ColSys X u' rows') (FdN FdN' : Set X.B.I.Ginf)
    (t : GTerm X u u' F0 F0' what₂ rows') (h : OOt t = 0) : aTerm cs cs' FdN FdN' t = 0 := by
  have hb : ∀ ρ ρ', blk cs cs' FdN FdN' t ρ ρ' = 0 := by
    intro ρ ρ'
    simp [blk, h]
  ext φ : 1
  simp [aTerm, aTermL, hb]
  try rfl

theorem fundOf_spec {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)} {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
    (hF : FundExists X u u' F0 F0' what₂ rows') (t : GTerm X u u' F0 F0' what₂ rows') :
    IsSFund X.B.I (ROinf t) (FundOf t) := by
  unfold FundOf
  split_ifs with h0
  · exact h0.choose_spec
  · exact absurd (hF t) h0

theorem OOt_eq_zero (hRR : RelRepC) (hCov : CovRepC) (hSch : SchurNFC) (Y : Full X) {u u' : D.what₂.Word}
    (hw : ∀ τ, uS D u τ ≠ uS D u' τ)
    (hF : FundExists X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'))
    (hI : OOIntAll X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'))
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (hr : t.relevant) (hG : t.G = 0) :
    OOt t = 0 := by
  obtain ⟨hrel, hG0⟩ := hRR D X Y u u' t hr hG
  have hfs := fundOf_spec hF t
  have hcov := hCov D X u u' t.lam t.lam' t.rep hrel (FundOf t) hfs (hI t)
  exact hSch D X u u' t.lam t.lam' t.rep hw hrel hG0 (OOt t) hcov

theorem kppTermZero_of_cut (hRR : RelRepC) (hCov : CovRepC) (hSch : SchurNFC) (hV : LemmaVC)
    (Y : Full X) {u u' : D.what₂.Word} (hw : ∀ τ, uS D u τ ≠ uS D u' τ)
    (hF : FundExists X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'))
    (hI : OOIntAll X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) :
    Formalism.L2.SG.RowsOther.KppTermZero (Y.tO u u') := by
  intro t ht
  have hG : t.G = 0 := by
    by_contra hne
    have h1 : Gt t = 0 := ht.1
    simp [Gt, hne] at h1
  have ha : aTerm (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t = 0 := by
    by_cases hr : t.relevant
    · exact aTerm_eq_zero_of_OOt _ _ _ _ t (OOt_eq_zero hRR hCov hSch Y hw hF hI t hr hG)
    · exact hV D X Y u u' hF hI t hr
  show Formalism.L2.SG.PackageTie.hsEmb (aTerm (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t) = 0
  rw [ha, map_zero]

theorem kppOffC_of_cut (hFold : FoldOKC) (hFE : FundExistsC) (hOI : OOIntAllC) (hV : LemmaVC)
    (hRR : RelRepC) (hCov : CovRepC) (hSch : SchurNFC) : Formalism.L2.SG.RowsConc.KppOffC := by
  intro Cg cb Cw cT CT C0
  refine ⟨0, 0, ?_⟩
  intro C' Cl _ _ D large₂ X Y u u' hH hT huu
  have hWu := hT.2.2.2.2.1
  have hFu := hFold D X Y u hT.1 hWu
  have hFu' := hFold D X Y u' hT.1 hWu
  exact kppTermZero_of_cut hRR hCov hSch hV Y (words_differ hH huu) (hFE D X Y u u')
    (hOI D X Y u u' hFu hFu' (hFE D X Y u u'))

end Asm

end Formalism.L2.SG.KappaOffDiagonal
