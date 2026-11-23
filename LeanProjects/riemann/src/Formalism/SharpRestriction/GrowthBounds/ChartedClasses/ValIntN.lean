import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.ClsChartedLabAt
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.CompInjLocJ

noncomputable section

namespace Formalism.MainNotions.G.KAat

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Formalism.MainNotions.G.CmpJ
  Formalism.MainNotions.G.CmpJ.PStabEq
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X0 : Formalism.L2.Herm.Herm0 D) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
  (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Fills (D.gat u w h)} (Lv : Levels Fl)

structure AtIn where
  Fo : ∀ j (hj : j + 1 ≤ D.R.m), FormsIn (Tw.fm u μ) (j + 1) hj
  Lc : ∀ j (hj : j + 1 ≤ D.R.m), LocIn X0 u w h Lv j (Fo j hj).Ch

variable {X0 Tw u μ w h Lv}

def AtIn.st (Z : AtIn X0 Tw u μ w h Lv) (Gt : GatTies D) (j : ℕ) (hj : j + 1 ≤ D.R.m) :
    StepIn (Tw.fm u μ) (j + 1) hj (gatJ Lv (j + 1)) :=
  stepInOf hj (Z.Fo j hj) (Z.Lc j hj) (Gt.gat_pos u w h)

def AtIn.I (Z : AtIn X0 Tw u μ w h Lv) (Gt : GatTies D) : CmpJIn Tw u μ w h Lv := inTw (Z.st Gt)

structure AtHyp (Z : AtIn X0 Tw u μ w h Lv) (Gt : GatTies D) (c : LatCmp D) : Prop where
  fl_t : Fl.t = D.R.t
  fill : FillTie Gt u w h Fl
  ties : ∀ j hj β, LocTiesR hj (Z.Fo j hj) (Z.Lc j hj) (c.embW u w h) β
  hypC : ∀ j hj β, HypTJC ((Z.Lc j hj).t β)
  ok : ∀ j hj, (Z.st Gt j hj).okW w
  twUnit : ∀ j hj β, (Z.st Gt j hj).TwUnit w β
  valIntN : ∀ j hj, (Z.st Gt j hj).ValIntN (c.embW u w h) w
  fin : ∀ j, j + 1 ≤ D.R.m → (gatJ Lv (j + 1)).FinClasses
  card : ∀ j (hj : j + 1 ≤ D.R.m), Fintype.card ((Tw.fm u μ).lat (j + 1)).ι = Module.finrank (D.gat u w h).O (gatJ Lv (j + 1)).M

variable {Gt : GatTies D} {c : LatCmp D} {T : ∀ u : D.what₂.Word, Forms0 D u}

theorem AtHyp.hyp {Z : AtIn X0 Tw u μ w h Lv} (A : AtHyp Z Gt c) (K : CmpTied D X0 T Gt c) : CmpJHyp c (Z.I Gt) where
  core := fun j hj β => core_of_R hj K A.fl_t A.fill (A.ties j hj β)
  ok := A.ok
  twUnit := A.twUnit
  valIntN := A.valIntN
  iwF := fun j hj β => iwF_of hj (Z.Fo j hj) (Z.Lc j hj) (Gt.gat_pos u w h) β
  fin := A.fin
  card := A.card

theorem AtHyp.chX {Z : AtIn X0 Tw u μ w h Lv} (A : AtHyp Z Gt c) (j : ℕ) (hj : j + 1 ≤ D.R.m) : ChX (((Z.I Gt).at' j hj).st) :=
  chX_stepInOf hj (Z.Fo j hj) (Z.Lc j hj) (Gt.gat_pos u w h) (fun β => (A.ties j hj β).sameU) (fun β => (A.ties j hj β).frRat)
    (A.hypC j hj)

def AtHyp.lab {Z : AtIn X0 Tw u μ w h Lv} (A : AtHyp Z Gt c) (fl_m : Fl.mm = D.R.m) (c0 : Formalism.L2.G.TwTie0.ClsAt0 D u μ w h Lv)
    (fill : ∀ j, D.R.m < j → Lv.comp j → (D.chTw u μ).cls j) (rat : ∀ j, j < D.R.m → (Tw.fm u μ).KRat j)
    (dgam : (D.chTw u μ).DGam ∣ (D.mem u).C.DGam) : LabIn (Z.I Gt) where
  onCh := fun _ _ => rfl
  chX := A.chX
  fl_t := A.fl_t
  fl_m := fl_m
  c0 := c0
  fill := fill
  rat := rat
  dgam := dgam

def kaAtZ {Z : AtIn X0 Tw u μ w h Lv} (A : AtHyp Z Gt c) (K : CmpTied D X0 T Gt c) (fl_m : Fl.mm = D.R.m)
    (c0 : Formalism.L2.G.TwTie0.ClsAt0 D u μ w h Lv) (fill : ∀ j, D.R.m < j → Lv.comp j → (D.chTw u μ).cls j)
    (rat : ∀ j, j < D.R.m → (Tw.fm u μ).KRat j) (dgam : (D.chTw u μ).DGam ∣ (D.mem u).C.DGam) :
    TwTie.KerAtMu D c Tw u μ w h (chainAt (A.hyp K) Gt) :=
  kaAt (A.lab fl_m c0 fill rat dgam) (A.hyp K) Gt

end Formalism.MainNotions.G.KAat

end
