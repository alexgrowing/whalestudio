import Formalism.LocalToGlobal.ThetaChr
import Formalism.LocalToGlobal.HermitianForms.BothSym
import Formalism.LocalToGlobal.HermitianForms.ExtraSym
import Formalism.LocalToGlobal.HermitianForms.TiedTwSymAll
import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.GroupLattices.StdSubAtOfRing
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Formalism.LocalToGlobal.LatticeGeometry.GeoTied
import Formalism.LocalToGlobal.LatticeGeometry.GeoTiedP
import Formalism.SharpRestriction.PageFix
import Formalism.SharpRestriction.Divisibility.SmallFirstModulusBelowScale
import Formalism.SharpRestriction.LevelLetterCocycles.AlignN

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions

namespace Formalism.L2

section

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC}

structure LinkedFamilyData (ex : Extra D L hT Gi Gl K Y cX) where
  host : Host.HostTied D
  level : Host.LevelTied D

  cols : Forms.ColsTiedSym D

  full : Forms.ColsFullS cols

  extra : Forms.ColsExtraTiedS full ex
  provA : TH.ProvA
  theta : Theta.AllTied D ex.th provA
  twIn : TwIn D
  n : NormalizedTwistCompatibility D ex.nch twIn
  frameN : Host.SameFrameN host n.gal.fr.jE
  thetaChr : Host.ThetaChrTied D n.cf ex.nch n.tp ex.th
  chrVal : Host.ValLL0 D n.cf
  chrDt : Host.DtTied D n.cf
  chrN : Host.NCharTied D n.cf ex.nch n.tp
  chrGal : Host.NGalChrTied D n.cf ex.nch n.tp
  chrPsi : Host.PsiChoiceCompatible D n.cf ex.nch n.tp
  sameChr : JoinChr.SameChr theta.T thetaChr
  what₂ : Rows.RowsCompatible D host n.cf n.tp

  inK : Y.Lev → ℕ → Prop

  geo : Geo.GeoTiedP Y inK

  tw : Forms.SymmetricTwistedColumnsAtPrimes n.tp cols ex.tw

  emt : Rows.EMtTied D cols tw

  g : G.GroupCompatibilityAll D hT ex.cmp
  herm_eq : g.herm = full.1.to0
  forms_eq : g.forms = fun u => (cols.forms u).to0

def LinkedFamilyCondition (ex : Extra D L hT Gi Gl K Y cX) : Prop := Nonempty (LinkedFamilyData ex)

def LinkedDataOneLevel (ex : Extra D L hT Gi Gl K Y cX) : Prop :=
  ∃ T : LinkedFamilyData ex, ∃ C : Forms.OneLevelSymmetricColumns D, C.toColsTiedSym = T.cols

end

def LinkedFamiliesLevelClass : FamClass := fun {_} Fm =>
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, LinkedFamilyCondition (Fm.ex x hx i)

def LinkedFamiliesOneLevel : FamClass := fun {_} Fm =>
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, LinkedDataOneLevel (Fm.ex x hx i)

def LinkedFamiliesFixedValues : FamClass := Formalism.MainNotions.WithPage LinkedFamiliesLevelClass

def LinkedFamiliesAligned : FamClass := fun {_} Fm =>
  LinkedFamiliesFixedValues Fm ∧ Formalism.MainNotions.DIV.Align.SmallFirstModulusBelowScale Fm ∧
    Formalism.MainNotions.TameDistinctF Fm

theorem LinkedFamiliesAligned.c2s {eps : ℝ} {Fm : FamP eps} (h : LinkedFamiliesAligned Fm) : LinkedFamiliesLevelClass Fm := h.1.1

theorem LinkedFamiliesOneLevel.c2s {eps : ℝ} {Fm : FamP eps} (h : LinkedFamiliesOneLevel Fm) : LinkedFamiliesLevelClass Fm := by
  obtain ⟨x0, h⟩ := h
  exact ⟨x0, fun x hx hx0 i => let ⟨T, _⟩ := h x hx hx0 i; ⟨T⟩⟩

end Formalism.L2
