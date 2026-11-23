import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ValIntN
import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK

noncomputable section

namespace Formalism.MainNotions.G.KAat

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.AgreeLv
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Tw : TwForms D} {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop}
  {T : Formalism.L2.Herm.TwChTied D inQ} {Hc : Formalism.L2.Herm.HermColsCh D} {J : Formalism.L2.Herm.TwChJointS T Hc}
  {F : ∀ u, FormsTiedSym D u (Hc.Ch u) (Hc.chOf u)}
  {X0 : Formalism.L2.Herm.Herm0 D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

def ClsCharted1 (T : Formalism.L2.Herm.TwChTied D inQ) (K : KerLabelsMu Tw u μ w h Lv) (ch : ∀ j, Lv.comp j → T.Ch u μ j) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ (a : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L → T.chOf u μ j (K.cls j a L) = ch j a

theorem yb_cls {K : KerLabelsMu Tw u μ w h Lv} {ch : ∀ j, Lv.comp j → T.Ch u μ j} (hC : ClsCharted1 T K ch) (h1 : 1 ≤ D.R.m - 1)
    (a : Lv.comp (D.R.m - 1)) (L : (Fl.Pj (D.R.m - 1)).Tup) (hL : (Fl.Pj (D.R.m - 1)).IsLatTup L) :
    T.yb u μ h1 (T.chOf u μ (D.R.m - 1) (K.cls (D.R.m - 1) a L)) = ybOf T ch h1 a := by
  unfold ybOf
  rw [hC (D.R.m - 1) h1 (Nat.sub_le _ _) a L hL]

def atInTw (W : TwFormsTiedS D Tw T J F) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0) {w : D.what₂.places.Pl}
    {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}
    (dt : ∀ j (hj : j + 1 ≤ D.R.m) β, DetTie (W.ch u μ hμ (j + 1) (one_le j) hj β).lev)
    (Lc : ∀ j (_ : j + 1 ≤ D.R.m), LocIn X0 u w h Lv j (T.Ch u μ (j + 1))) : AtIn X0 Tw u μ w h Lv where
  Fo := fun j hj => formsInTw W u μ hμ j hj (dt j hj)
  Lc := Lc

variable (W : TwFormsTiedS D Tw T J F) (hμ : μ ≠ D.what₂.mu0)
  (dt : ∀ j (hj : j + 1 ≤ D.R.m) β, DetTie (W.ch u μ hμ (j + 1) (one_le j) hj β).lev)
  (Lc : ∀ j (_ : j + 1 ≤ D.R.m), LocIn X0 u w h Lv j (T.Ch u μ (j + 1)))

def chTie_atInTw (Gt : GatTies D) : ChTie T ((atInTw W u μ hμ dt Lc).st Gt) where
  eCh := fun _ _ β => β
  chOf := fun _ _ _ => rfl

variable {W hμ dt Lc}

theorem clsCharted1_atInTw {Gt : GatTies D} {c : LatCmp D} (X : LabIn ((atInTw W u μ hμ dt Lc).I Gt))
    (H : CmpJHyp c ((atInTw W u μ hμ dt Lc).I Gt)) (ch : ∀ j, Lv.comp j → T.Ch u μ j)
    (hch : ∀ j (hj : j + 1 ≤ D.R.m) a, ch (j + 1) a = ((Lc j hj).eC.symm a).1) : ClsCharted1 T (labAt X H) ch := by
  intro j h1 hj a L hL
  cases j with
  | zero => omega
  | succ j =>
    rw [hch j hj]
    exact labAt_chOf (st := (atInTw W u μ hμ dt Lc).st Gt) X H j hj a L hL

end Formalism.MainNotions.G.KAat

end
