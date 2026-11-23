import Formalism.SharpRestriction.GrowthBounds.ChartComparison.OneChartLev
import Formalism.SharpRestriction.GrowthBounds.ChartComparison.BadQNotOver

noncomputable section

namespace Formalism.MainNotions.G.CmpJ

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} {p : ℕ}

structure MemStep (F : FormsTiedSym D u Ch chOf) (i : ℕ) (h1 : 1 ≤ i) (hi : i ≤ D.R.m) (G : GAtP p) where

  dtTop : ∀ h : i = D.R.m, DetTie (F.cls i hi (Or.inr h)).lev
  locTop : i = D.R.m → LocPart D G Unit (D.R.N i)

  dtMid : ∀ (h2 : i + 1 ≤ D.R.m) (β : Ch i), DetTie (F.ch i h1 h2 β).lev
  locMid : i + 1 ≤ D.R.m → LocPart D G (Ch i) (D.R.N i)

open Classical in

def stepInMem (F : FormsTiedSym D u Ch chOf) (i : ℕ) (h1 : 1 ≤ i) (hi : i ≤ D.R.m) (G : GAtP p) (X : MemStep F i h1 hi G) :
    StepIn (D.fm u) i hi G :=
  if h : i = D.R.m then
    stepInOne (F.val i hi (Or.inr h)) G (X.dtTop h) (X.locTop h).cmpt (X.locTop h).eC (X.locTop h).loc (X.locTop h).pos
  else
    stepInMid F i h1 (by omega) G (X.dtMid (by omega)) (X.locMid (by omega)).cmpt (X.locMid (by omega)).eC
      (X.locMid (by omega)).loc (X.locMid (by omega)).pos

theorem stepInMem_top (F : FormsTiedSym D u Ch chOf) (i : ℕ) (h1 : 1 ≤ i) (hi : i ≤ D.R.m) (G : GAtP p) (X : MemStep F i h1 hi G)
    (h : i = D.R.m) : stepInMem F i h1 hi G X =
      stepInOne (F.val i hi (Or.inr h)) G (X.dtTop h) (X.locTop h).cmpt (X.locTop h).eC (X.locTop h).loc (X.locTop h).pos :=
  dif_pos h

theorem stepInMem_mid (F : FormsTiedSym D u Ch chOf) (i : ℕ) (h1 : 1 ≤ i) (hi : i ≤ D.R.m) (G : GAtP p) (X : MemStep F i h1 hi G)
    (h2 : i + 1 ≤ D.R.m) : stepInMem F i h1 hi G X =
      stepInMid F i h1 h2 G (X.dtMid h2) (X.locMid h2).cmpt (X.locMid h2).eC (X.locMid h2).loc (X.locMid h2).pos :=
  dif_neg (by omega)

theorem stepInMem_ok (F : FormsTiedSym D u Ch chOf) (i : ℕ) (h1 : 1 ≤ i) (hi : i ≤ D.R.m) (G : GAtP p) (X : MemStep F i h1 hi G)
    (w : D.what₂.places.Pl) : (stepInMem F i h1 hi G X).okW w := by
  by_cases h : i = D.R.m
  · rw [stepInMem_top F i h1 hi G X h]
    trivial
  · rw [stepInMem_mid F i h1 hi G X (by omega)]
    trivial

theorem stepInMem_bad (F : FormsTiedSym D u Ch chOf) (i : ℕ) (h1 : 1 ≤ i) (hi : i ≤ D.R.m) (G : GAtP p) (X : MemStep F i h1 hi G) :
    (stepInMem F i h1 hi G X).bad = badG D := by
  by_cases h : i = D.R.m
  · rw [stepInMem_top F i h1 hi G X h]
    rfl
  · rw [stepInMem_mid F i h1 hi G X (by omega)]
    rfl

end Formalism.MainNotions.G.CmpJ

end
