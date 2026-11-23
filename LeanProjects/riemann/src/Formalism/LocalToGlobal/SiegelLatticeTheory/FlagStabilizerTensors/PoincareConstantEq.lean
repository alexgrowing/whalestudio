import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermOpStmt
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.Saturated
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.WuDecay

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp

set_option linter.dupNamespace false

namespace Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Defs

variable {D : D7} (X : HidaSetting D)

end Defs

structure Full {D : D7} (X : HidaSetting D) where
  hK : X.LevelSubgroupCharacter
  TR : TypedRed X
  psi_ne : ∀ v, TR.psi0 v ≠ 1
  what₂ : D.what₂.Word → Finset (Submodule (𝓞 D.host.E) (VS D).V)
  rowsOK : ∀ u, IsRowReps D (X.Fu u) (what₂ u)
  split : ∀ u, ∀ Λ ∈ what₂ u, Formalism.L2.SG.Saturated.IsSplitRow D (X.Fu u) Λ
  cs : ∀ u, ColSys X u (what₂ u)
  colReps : ∀ u, ColReps hK (cs u)
  Dt : D.what₂.Word → Set X.B.I.GA
  reps : ∀ u, IsReps X u (Dt u)
  FN : D.what₂.Word → Set X.B.I.Ginf
  FN_fund : ∀ u, IsSFund X.B.I (NOinf X u) (FN u)

  δ : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, (D.s.atP p).Fp
  M : ∀ p : Formalism.MainNotions.S.LocalSplitGroups.PlF D, Formalism.MainNotions.S.Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep
  agree : ∀ p, Formalism.MainNotions.S.LocalSplitGroups.Agree δ M p

  δ_pin : ∀ (p : Formalism.MainNotions.S.LocalSplitGroups.PlF D) (i : Fin 2), ((D.host.g i : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal →
    δ p = (D.s.atP p).ιF (((D.host.g 0 : ℕ) : D.host.F) * ((D.host.g 1 : ℕ) : D.host.F) / ((D.host.g i : ℕ) : D.host.F))

namespace Full

variable {D : D7} {X : HidaSetting D} (Y : Full X)

def volN (u : D.what₂.Word) : ℝ := X.volK2 * ((X.muN u) (Y.FN u)).toReal

def volH (_Y : Full X) (u : D.what₂.Word) : ℝ := ((X.muH u) Set.univ).toReal

abbrev tO (u u' : D.what₂.Word) :=
  tOf (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u')

theorem poincare_constant_eq (u : D.what₂.Word) : c0X X u (Y.FN u) = Y.volN u * Y.volH u / (Module.finrank ℂ (X.Vpi u) : ℝ) := by
  unfold c0X volN volH
  rfl

theorem frameTie (u u' : D.what₂.Word) : FrameTie X u u' (X.Fu u) (X.Fu u') :=
  ⟨fun a => congrFun (X.Fu_e u) a, X.flagZVector u, fun a => congrFun (X.Fu_e u') a, X.flagZVector u'⟩

end Full

section Closed

open Full

def FullExists : Prop := ∀ (D : D7) (X : HidaSetting D), X.LevelSubgroupCharacter → Nonempty (Full X)

def VolPosC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), X.LevelSubgroupNormalized → 0 < Y.volN u ∧ 0 < Y.volH u

def FoldOKC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
    X.LevelSubgroupNormalized → Formalism.L2.SG.WuDecay.WuDecay X → Formalism.L2.SG.WuDecay.FoldOK X u Y.hK

def InHHC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
    Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) →
    Formalism.L2.SG.WuDecay.FoldOK X u Y.hK → InHH X u Y.hK

def PuLinearC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word), PuLinear X u Y.hK (Y.Dt u)

def FundExistsC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    FundExists X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')

def OOIntAllC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    Formalism.L2.SG.WuDecay.FoldOK X u Y.hK → Formalism.L2.SG.WuDecay.FoldOK X u' Y.hK →
    FundExists X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    OOIntAll X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')

def OOFundIndepC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    FundExists X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    OOIntAll X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    OOFundIndep X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')

def AmpWellDefC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    OOIntAll X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    AmpWellDef (X.Fu u) (X.Fu u') (Y.cs u) (Y.cs u')

def ChiNIndepC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    ChiNIndep (X.Fu u) (X.Fu u') (Y.cs u) (Y.cs u')

def LemmaVC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    FundExists X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    OOIntAll X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    LemmaV (X.Fu u) (X.Fu u') (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u')

def KExpansionC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    Formalism.L2.SG.WuDecay.FoldOK X u Y.hK → Formalism.L2.SG.WuDecay.FoldOK X u' Y.hK →
    InHH X u Y.hK → InHH X u' Y.hK →
    FundExists X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    OOIntAll X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    OOFundIndep X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    AmpWellDef (X.Fu u) (X.Fu u') (Y.cs u) (Y.cs u') →
    AbsConvT (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') →
    Formalism.L2.SG.TermOp.KExpansion (X.Fu u) (X.Fu u') (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') Y.hK
      (Y.Dt u) (Y.Dt u')

def AbsConvC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    Formalism.L2.SG.WuDecay.FoldOK X u Y.hK → Formalism.L2.SG.WuDecay.FoldOK X u' Y.hK →
    FundExists X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    OOIntAll X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    AbsConvT (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u')

def NormExpSatC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    AmpWellDef (X.Fu u) (X.Fu u') (Y.cs u) (Y.cs u') →
    ChiNIndep (X.Fu u) (X.Fu u') (Y.cs u) (Y.cs u') →
    AbsConvT (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') →
    NormExpSat (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u')

def IdCellOffC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    FundExists X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    OOIntAll X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') →
    Formalism.L2.SG.TermOp.IdCellOff (X.Fu u) (X.Fu u') (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u')

def IdCellDiagC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u : D.what₂.Word),
    X.LevelSubgroupNormalized →
    FundExists X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u) →
    OOIntAll X u u (X.Fu u) (X.Fu u) (Y.what₂ u) (Y.what₂ u) →
    Formalism.L2.SG.TermOp.IdCellDiag (X.Fu u) (Y.cs u) (Y.FN u)

end Closed

end Formalism.L2.SG.Full
