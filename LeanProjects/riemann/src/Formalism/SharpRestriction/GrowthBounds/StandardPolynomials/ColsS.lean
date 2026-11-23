import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColDef
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.SymbolEq

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.LemmaBAlt Formalism.MainNotions.ColumnSystems.Pf.Col

section

variable (C0 CE1 CE2 mu : ℝ) (X : Loc) (β : GlobalTheory X) (j : Fin (numSeg X.TT))

def zxS (l : Fin (segS X.TT j)) : ℕ :=
  coarseA X.p (X.seg C0 CE1 CE2 j) (β j) l -
    (if (l : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (β j).w l else (β j).o l)

def a0Z : ℤ :=
  ⌊(((X.seg C0 CE1 CE2 j).A0 X.p : ℤ) : ℝ) - mu⌋ -
    ∑ l : Fin (segS X.TT j), (if (l : ℕ) < (X.seg C0 CE1 CE2 j).sigma then ((β j).sg l : ℤ) else 0)

def nuS (T : ℕ) : ℤ :=
  if T = 0 then 0 else a0Z C0 CE1 CE2 mu X β j +
    ∑ l : Fin (segS X.TT j), (if 2 * (l : ℕ) + 2 ≤ T then (zxS C0 CE1 CE2 X β j l : ℤ) else 0)

end

def PS (X : Loc) (j : Fin (numSeg X.TT)) (t : Fin (2 * segS X.TT j + 1 + 1)) : ℕ := X.p ^ (zS X j - posS X j t).toNat

section

variable (C0 CE1 CE2 mu : ℝ) (X : Loc) (β : GlobalTheory X) (j : Fin (numSeg X.TT))
  (ka : Fin (2 * segS X.TT j + 1 + 1) → Fin X.m → ℤ)

def colsS : Finset ℤ := colRange ka ∪ Finset.Icc 1 (nuS C0 CE1 CE2 mu X β j (2 * segS X.TT j + 1 + 1))

def plS (c : ℤ) : MonH X :=
  ∑ t : Fin (2 * segS X.TT j + 1 + 1),
    if nuS C0 CE1 CE2 mu X β j t.val < c ∧ c ≤ nuS C0 CE1 CE2 mu X β j (t.val + 1) then
      Finsupp.single (phiS X j (t, Fin.castAdd X.m 0)) (PS X j t) else 0

def dKS (c : ℤ) (i : Fin (2 * segS X.TT j + 1)) : ℕ := if colH (ka i.castSucc) c = colH (ka i.succ) c then 0 else 1

def oCS (c : ℤ) : ℕ := oc (PS X j) (muP (nuS C0 CE1 CE2 mu X β j) ka) c

def dgCS (c : ℤ) (l : X.TT × Bool) : ℕ :=
  ∑ t : Fin (2 * segS X.TT j + 1 + 1), if lamS X j t = l then
    dgS X.p (posS X j) (muP (nuS C0 CE1 CE2 mu X β j) ka) c (2 * segS X.TT j + 1 + 1) (zS X j) t else 0

def fCS [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (I'' : ℤ → Finset (Fin X.m)) (c : ℤ) :
    RHH O X :=
  rename (phiS X j) (KKc X.p X.n' (O := O) (LLseg X j) 1 (zS X j) (muP (nuS C0 CE1 CE2 mu X β j) ka) c
    (Jc (nuS C0 CE1 CE2 mu X β j) (2 * segS X.TT j + 1) c (I'' c)))

end

end Formalism.MainNotions.ColumnSystems.Pf
