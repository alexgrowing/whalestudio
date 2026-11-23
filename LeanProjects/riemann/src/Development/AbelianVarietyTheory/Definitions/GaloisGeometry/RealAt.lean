import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Realises

noncomputable section

namespace GlobalTheory.TwV.DelA

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG
open Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.KerInert.QuadraticBaseChangeGL3 GlobalTheory.TwV.DelB

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)}
  {Lv : Levels (Gl.Fl u w hg)} {I : CmpJIn ex.tw u μ w hg Lv} {H : CmpJHyp ex.cmp I} {X : LabIn I}
  [Fact (D.what₂.places.resChar w).Prime] {t : KerEntTied ex} (J : Joint t H X) (std : Lt.StdAtW D Gl u w hg)

def bAt : ∀ (j : ℕ) (_ : j ≤ D.R.m), Lv.comp j → GL (Fin (D.R.N j)) D.host.E
  | 0, _, _ => (lev0At J.Gd u w hg).A.B
  | j + 1, hj, a => ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm a).1).B

def uB (j : ℕ) (hj : j ≤ D.R.m) (a : Lv.comp j) : GL (Fin (D.R.N j)) D.host.E := J.A.crd j hj * bAt J j hj a

def dPow {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) (a : D.what₂.Tau → ℤ) : ℂ := ∏ τ, embT D τ M.det ^ a τ

variable {J std}

def mM (d : Dec J std) (j : ℕ) (hj : j ≤ D.R.m) (La : (sysS H X std).Lt j) : GL (Fin (D.R.N j)) D.host.E :=
  J.A.crd j hj * (d.gam j hj La)⁻¹ * bAt J j hj La.1

def sPt (d : Dec J std) (j : ℕ) (hj : j ≤ D.R.m) (La : (sysS H X std).Lt j) : ℂ :=
  d.chi j hj La * ((D.chiD ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) ^ cTw D j *
    dPow (uB J j hj La.1).1 (fun _ => -(cTw D j))

def RealAt (d : Dec J std) (j : ℕ) (hj : j ≤ D.R.m) (h : ((sysS H X std).Pj j).m + 1 = D.R.N j) (La : (sysS H X std).Lt j)
    (φ : (D.chTw u μ).cls j → (D.chTw u μ).Y j → ℂ) (V : XR ((sysS H X std).Pj j) ℂ) : Prop :=
  ∀ z z' : Fr D j hj, IsTr (atInf (embT D) (d.gam j hj La).1) z' z →
    evC ((sysS H X std).Pj j) h (posJ (sysS H X std) D (hT.gat_pos u w hg) j) (gramC (gramN D j hj) (embT D)) (crdB (embT D) (bAt J j hj La.1)) V z =
      d.chi j hj La * ((D.chiD ((t.O u μ).dt j (clsAt X H j La.1 La.2)) : ℂˣ) : ℂ) ^ cTw D j *
        dPow (bAt J j hj La.1).1 (fun _ => -(cTw D j)) * detF (cTw D j) z' *
        φ (clsAt X H j La.1 La.2) ((J.St j hj).eY.symm z')

open Classical in

def sO (d : Dec J std) (ι : ℂ →+* ℂ_[D.what₂.places.resChar w]) (j : ℕ) (La : (sysS H X std).Lt j) : ℂ_[D.what₂.places.resChar w] :=
  if hj : j ≤ D.R.m then ι (sPt d j hj La * cOp (sysS H X std) D (hT.gat_pos u w hg) j (t.O u μ).dgen) else 0

def gmS (d : Dec J std) (j : ℕ) (La : (sysS H X std).Lt j) (x : ((ex.tw.fm u μ).lat j).V) : ((sysS H X std).Pj j).Xsp :=
  gmOf d.fd2 j La ((kaAt X H hT).cmp j x La.1 La.2)

variable (J std)

def kS (j : ℕ) (hj : j ≤ D.R.m) (a : Lv.comp j) : ℂ :=
  dPow (uB J j hj a).1 (fun τ => -((D.chTw u μ).sSharp j τ)) *
    dPow (gMat J j hj 1) (fun _ => ((D.R.N (j + 1) / 2 : ℕ) : ℤ) + cTw D j)

def kT (j : ℕ) (hj : j + 1 ≤ D.R.m) (a : Lv.comp (j + 1)) : ℂ :=
  dPow (uB J (j + 1) hj a).1 (fun τ => -((D.chTw u μ).sDiv j τ)) *
    dPow (gMat J (j + 1) hj 1) (fun _ => ((D.R.N j / 2 : ℕ) : ℤ) + cTw D (j + 1))

variable {J std}

def cKs (S : J.At std) (ι : ℂ →+* ℂ_[D.what₂.places.resChar w]) (j : ℕ) (hj : j + 1 ≤ D.R.m) (a : Lv.comp j) (a' : Lv.comp (j + 1)) :
    ℂ_[D.what₂.places.resChar w] :=
  ι (kT J j hj a' * (kS J j (Nat.le_of_succ_le hj) a * cOp (sysS H X std) D (hT.gat_pos u w hg) j (t.O u μ).dgen)⁻¹) *
    ltC S.g S.hLT ^ (-(∑ τ, szT (sysS H X std) D (hT.gat_pos u w hg) j τ))

open Classical in

def scT (d : Dec J std) (S : J.At std) (ι : ℂ →+* ℂ_[D.what₂.places.resChar w]) (j : ℕ) (c' : Lv.comp (j + 1))
    (L' : ((sysS H X std).Pj (j + 1)).Tup) : ℂ_[D.what₂.places.resChar w] :=
  if hj : j + 1 ≤ D.R.m then
    ι (d.uT S j (c', L') * kT J j hj c') * ltC S.g S.hLT ^ (-(∑ τ, szT (sysS H X std) D (hT.gat_pos u w hg) j τ))
  else 0

end GlobalTheory.TwV.DelA

end
