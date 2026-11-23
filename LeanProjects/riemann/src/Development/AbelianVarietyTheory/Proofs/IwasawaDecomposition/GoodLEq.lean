import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DofOTw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideTw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AutomorphicSideTransfer
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.HeightCounting.Up.LiTw

section Gen

variable {D : D7} (N : TwNew D)

def sideA {cf : CharFrame D} {jE : D.host.E →+* Qb} (A : SideA D cf jE) : SideA N.toD7 (N.cf cf) jE :=
  { bare := A.bare
    wdT := A.wdT
    lab := A.lab
    chr := { A.chr with }
    row := N.row A.row
    pl := { A.pl with }
    iota := A.iota
    wd := { A.wd with }
    grp := { A.grp with }
    par := { A.par with }
    au := { A.au with }
    chiT := A.chiT }

def stA {hL : GlobalTheory.Published.LocalLanglandsGL} {cf : CharFrame D} {rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r} (a : StA hL D cf rep)
    (rep' : N.toD7.what₂.FT → NG.FinTyp N.toD7.host.E N.toD7.R.r) (e : HEq rep' rep) :
    StA hL N.toD7 (N.cf cf) rep' where
  host := ⟨a.host.fr, a.host.jLL, a.host.embLL⟩
  jE := a.jE
  frame := a.frame
  A := sideA N a.A
  cg := { a.cg with }
  au := a.au
  row := by obtain rfl : rep' = rep := eq_of_heq e; exact a.row
  fr := ⟨a.fr.jE, a.fr.eOm, a.fr.comm⟩
  fr_jE := a.fr_jE
  pht := { a.pht with }
  depth := by obtain rfl : rep' = rep := eq_of_heq e; exact a.depth
  elem := { a.elem with }
  val := { a.val with }
  labc := a.labc
  zeta := a.zeta
  omax := a.omax

theorem goodL_eq (S : RatDat D.ntw) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (j : ℕ) :
    goodL N.toD7 (N.rat S) θ j = goodL D S θ j := by
  have h : N.ex.eLL0 = D.nexp.eLL0 := funext fun g =>
    Subtype.ext (D.what₂.embLL.injective ((N.h0 g).trans (D.nStage_trivialCharacter_coeff_eq g).symm))
  exact congrArg (fun e : G0g D.nd → ↥D.LL0 =>
    Module.End.eigenspace (∑ᶠ g : G0g D.nd, ((e g : ↥D.LL0) : D.what₂.LL) • actL D S j g) 1 ⊓
    ⨅ u : Formalism.IndefR.NX.U D.nd, Module.End.eigenspace (actL D S j u)
      (((psiUOf D.nd (NX.xiRed D) θ u : (↥D.LL0)ˣ) : ↥D.LL0) : D.what₂.LL)) h

def ratIn {S : RatDat D.ntw} (I : RatIn D S) : RatIn N.toD7 (N.rat S) where
  Sb := I.Sb
  rho := I.rho
  chi := I.chi
  ks := I.ks
  fd := I.fd
  mk_fg := I.mk_fg
  hL := I.hL
  hs := I.hs
  hL_zero := I.hL_zero
  θ := I.θ
  θ_ne := I.θ_ne
  eig := I.eig
  span := fun j h1 h2 => by rw [goodL_eq N S I.θ j]; exact I.span j h1 h2
  hL_int := fun j k P h1 h2 => by rw [goodL_eq N S I.θ j]; exact I.hL_int j k P h1 h2

theorem cusp {Rw : RowSide D} (h : RowCusp D Rw) : RowCusp N.toD7 (N.row Rw) := h

theorem mtIn {M tup Q} (h : MtInput D M tup Q) : MtInput N.toD7 (N.mt M) tup Q := { h with }

end Gen

end GlobalTheory.HeightCounting.Up.LiTw

end
