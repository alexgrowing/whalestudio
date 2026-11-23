import Formalism.SharpRestriction.GrowthBounds.ChartComparison.KerLabelsMu
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.BadQNotOver

noncomputable section

namespace Formalism.MainNotions.G.CmpJ

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.Forms NumberField IsDedekindDomain

variable {D : D7} {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop} (T : Formalism.L2.Herm.TwChTied D inQ)
  {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

def ClsCharted (K : KerLabelsMu Tw u μ w h Lv) (ch : ∀ j, Lv.comp j → T.Ch u μ j) : Prop :=
  ∀ j, j ≤ D.R.m → ∀ (a : Lv.comp j) (L : (Fl.Pj j).Tup), (Fl.Pj j).IsLatTup L → T.chOf u μ j (K.cls j a L) = ch j a

def ybOf (ch : ∀ j, Lv.comp j → T.Ch u μ j) (h1 : 1 ≤ D.R.m - 1) (a : Lv.comp (D.R.m - 1)) : T.Yb u μ h1 :=
  T.yb u μ h1 (ch (D.R.m - 1) a)

variable {T}

def chOfLoc {p : ℕ} {G : GAtP p} {j : ℕ} (Lp : LocPart D G (T.Ch u μ j) (D.R.N j)) (a : G.comp) : T.Ch u μ j := (Lp.eC.symm a).1

end Formalism.MainNotions.G.CmpJ

end
