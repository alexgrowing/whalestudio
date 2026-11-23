import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JointCmpEmbeddingY

noncomputable section

namespace GlobalTheory.TwV.Xc

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG
open Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV GlobalTheory.TwV
open GlobalTheory.TwU (ratA ssRec)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I} {t : KerEntTied ex}

def KIn (t : KerEntTied ex) : Prop := ∀ y : t.X.K, ∃ k : D.what₂.LL, D.what₂.embLL k = t.seam.σ₀ y

abbrev A0 (J : Joint t H X) : LocAt D.host.F D.host.E (D.R.N 0) (D.gat u w hg) := (lev0At J.Gd u w hg).A

def Spl (J : Joint t H X) : Prop := SplAlg (A0 J) ∧ ∀ j hj β, SplAlg ((I.at' j hj).st.loc β)

open Classical in

def chiI (J : Joint t H X) (x : (AfE D.host.F D.host.E)ˣ) : ℂ :=
  if h : ∃ y : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm, Matrix.GeneralLinearGroup.det y.1 = x then ((D.chiD (J.dtU h.choose) : ℂˣ) : ℂ) else 0

def IsUnifAt (J : Joint t H X) (v : Fin (D.gat u w hg).P.nV) (π : (AfE D.host.F D.host.E)ˣ) : Prop :=
  π ∈ U1 (sigD D) ∧ OneOff ((A0 J).pl v).1 π ∧ ordA (A0 J) v π = 1

variable [Fact (D.what₂.places.resChar w).Prime] (std : Lt.StdAtW D Gl u w hg) (J : Joint t H X)

def MoveBy (j : ℕ) (hj : j ≤ D.R.m) (c : (sysS H X std).Lv.comp j) (La : ((sysS H X std).Pj j).Tup) (γ : ((sysS H X std).Lv.lev j c).Γ)
    (g : GL (Fin (D.R.N j)) D.host.E) (κ : ((J.St j hj).K (J.chart std j hj (c, La))).lev.U) : Prop :=
  g ∈ UJ (sigD D : D.host.E →+* D.host.E) (gramN D j hj) ∧
  (J.pt std j hj (c, ((sysS H X std).Lv.lev j c).smul γ La)).1 = ratA D.host.F g * (J.pt std j hj (c, La)).1 * κ.1 ∧
  (∀ (hr : ((sysS H X std).Pj j).m + 1 = D.R.N j) (v : (sysS H X std).Pl),
    (J.fd std).frM j (c, La) v * (gamAt (sysS H X std) j c γ v : Matrix _ _ _) =
      (eMat hr (D.sp.cm.sig : D.host.E →+* D.host.E) (gramN D j hj) g).map (J.rho std v) * (J.fd std).frM j (c, La) v) ∧
  ∃ r : D.what₂.LL, D.what₂.embLL r = ((((J.St j hj).K (J.chart std j hj (c, La))).lev.chi κ : ℂˣ) : ℂ) ∧
    algebraMap (sysS H X std).G.O (sysS H X std).G.Kf ((((sysS H X std).Lv.lev j c).χ γ : (sysS H X std).G.Oˣ) : (sysS H X std).G.O) =
      ex.cmp.embW u w hg r

def FillAt (j : ℕ) (hj : j < D.R.m) : Prop :=
  ∀ e : D.what₂.Tau → ℤ, (∀ τ, ((e τ : ℤ) : ℚ) = (D.hc τ).e ⟨j, hj⟩) → ∀ (v : (sysS H X std).Pl) (s : Fin ((sysS H X std).G.P.n' v)),
    (sysS H X std).w v (j + 1) s = e (hT.gat_pos u w hg ⟨v, s⟩) - ((j * ((sysS H X std).t + 1) / 2 : ℕ) : ℤ) -
      (((((sysS H X std).Pj (j + 1)).m + 1) / 2 : ℕ) : ℤ)

def SameAway (v : (sysS H X std).Pl) (j : ℕ) (La Lb : (sysS H X std).Lt j) : Prop :=
  ((sysS H X std).Pj j).IsLatTup La.2 ∧ ((sysS H X std).Pj j).IsLatTup Lb.2 ∧ La.1 = Lb.1 ∧
    Function.update La.2 ((sysS H X std).vJ j v) ⊥ = Function.update Lb.2 ((sysS H X std).vJ j v) ⊥

omit [Fact (D.what₂.places.resChar w).Prime] in

def Sites (Q : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Dx cX} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
    {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv}
    {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] {std : Lt.StdAtW D Gl u w hg} {t : KerEntTied ex}
    {J : Joint t H X}, J.At std → Prop) : Prop :=
  ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Dx cX} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
    {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv}
    {H : CmpJHyp ex.cmp I} {X : LabIn I} [Fact (D.what₂.places.resChar w).Prime] {std : Lt.StdAtW D Gl u w hg} {t : KerEntTied ex}
    {J : Joint t H X} (S : J.At std), J.Dict std → Spl J → Q S

end GlobalTheory.TwV.Xc

end
