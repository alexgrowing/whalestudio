import Formalism.SharpRestriction.GrowthBounds.ChartComparison.AlgebraMapUnitZpow
import Formalism.SharpRestriction.GrowthBounds.LatticeMultiplicityLemmas.LatticeMultiplicityCheck.Retype

open Formalism.MainNotions.G Formalism.BasicNotions NumberField

noncomputable section

namespace Formalism.MainNotions.G.CmpJ

open Formalism.L2.G.Cmp

section Final

variable {D : D7} (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (w : D.what₂.places.Pl)
  (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) {Fl : Fills (D.gat u w h)} (Lv : Levels Fl)

structure KerLabelsMu where
  fl_t : Fl.t = D.R.t
  fl_m : Fl.mm = D.R.m
  cls : ∀ j, Lv.comp j → (Fl.Pj j).Tup → (D.chTw u μ).cls j
  cls_iff : ∀ j, j ≤ D.R.m → ∀ (a a' : Lv.comp j) (L L' : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    (Fl.Pj j).IsLatTup L' →
    (cls j a L = cls j a' L' ↔ a = a' ∧ ∃ γ : (Lv.lev j a).Γ, L' = (Lv.lev j a).smul γ L)
  cls_surj : ∀ j, j ≤ D.R.m → ∀ x : (D.chTw u μ).cls j, ∃ a L, (Fl.Pj j).IsLatTup L ∧ cls j a L = x
  stab_zero : ∀ (a : Lv.comp 0) (L : (Fl.Pj 0).Tup), (Fl.Pj 0).IsLatTup L →
    Nat.card {γ : (Lv.lev 0 a).Γ // (Lv.lev 0 a).smul γ L = L} = 1
  stab_dvd : ∀ j, j ≤ D.R.m → ∀ (a : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    0 < Nat.card {γ : (Lv.lev j a).Γ // (Lv.lev j a).smul γ L = L} ∧
      Nat.card {γ : (Lv.lev j a).Γ // (Lv.lev j a).smul γ L = L} ∣ (D.mem u).C.DGam
  rat : ∀ j, j < D.R.m → (Tw.fm u μ).KRat j

  stab_eq : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ (a : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L →
    Nat.card ((D.chTw u μ).stab j (cls j a L)) = Nat.card {γ : (Lv.lev j a).Γ // (Lv.lev j a).smul γ L = L}

variable {c Tw u μ w h Lv}

def kerAtMu_of (K : KerLabelsMu Tw u μ w h Lv) (X : StepsMu c Tw u μ w h Lv) (hd : DescUp c u w h Lv)
    (hs : ValScalar c u w h) (hf : LocFree Tw u μ w D.R.m) : TwTie.KerAtMu D c Tw u μ w h (chainMu X.up) where
  fl_t := K.fl_t
  fl_m := K.fl_m
  cls := K.cls
  cls_iff := K.cls_iff
  cls_surj := K.cls_surj
  stab_zero := K.stab_zero
  stab_dvd := K.stab_dvd
  cmp := X.up.cmp
  cmp_inj := X.up.inj
  cmp_zero := X.up.cmp_zero
  cmp_int := X.cmp_int hd
  cmp_K := chainMu_cmp_K X.up
  rat := K.rat
  val := X.up.val_of D.R.m le_rfl (X.cmp_int hd D.R.m le_rfl) hs hf

end Final

section Rec

variable {D : D7} {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

def kerAtMu (K : KerLabelsMu Tw u μ w h Lv) (X : StepsMu c Tw u μ w h Lv) (hd : DescUp c u w h Lv)
    (v : Fin (D.gat u w h).P.nV) : TwTie.KerAtMu D c Tw u μ w h (chainMu X.up) :=
  kerAtMu_of K X hd (valScalar_of_place c u w h v) (locFree Tw u μ w D.R.m)

end Rec

end Formalism.MainNotions.G.CmpJ

end
