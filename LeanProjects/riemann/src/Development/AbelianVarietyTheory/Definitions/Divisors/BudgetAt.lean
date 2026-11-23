import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop

namespace GlobalTheory.CovHt

section Steps

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (Y : Cov p i)

def ShortAt (PP C : ℝ) (u1 : AllWt.Weight (dat p i)) : Prop :=
  ∃ abelian₂ : ℝ, (∀ Z, ∃ (n : ℕ) (w : Fin n → cuspOn Y.U Z (wtOf (dat p i) u1 0)),
      IsShortGen (normOn Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0))
        (latOn Y.U Z (wtOf (dat p i) u1 0)) w abelian₂) ∧
    Real.log abelian₂ * (6 * dimFlag (dat p i) + 10 + lenT p i PP * (zed p i PP u1 + 2 * rhoB (dat p i) u1)) ≤ C * unitE p

def GeomAt (u1 : AllWt.Weight (dat p i)) : Prop :=
  ∀ Z, GoodOn Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0) ∧
    GlobalTheory.DegVal.BirOn Y.U Z (wtOf (dat p i) u1 0) ∧ (1 - rhoB (dat p i) u1) * Y.dg u1 Z ≤ delPrime Y.U Z u1

def MultAt (PP C : ℝ) (u1 : AllWt.Weight (dat p i)) : Prop :=
  ∃ cc : ℝ, 0 ≤ cc ∧ lenT p i PP * cc ≤ C * unitE p ∧
    ∀ Z, Mult Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z u1 (uPrime (dat p i) u1) cc

def BudgetAt (PP C : ℝ) (u1 : AllWt.Weight (dat p i)) : Prop :=
  Y.d.l₂.M'.primeFactors.card ≤ 15 ∧
  ∃ g : ℝ, WtGap (uPrime (dat p i) u1) g ∧ 0 ≤ errX (ell D) (uPrime (dat p i) u1) g ∧
    lenT p i PP * errX (ell D) (uPrime (dat p i) u1) g ≤ C * unitE p ∧
    0 ≤ htCost Y.d.l₂ (bndB (uPrime (dat p i) u1) g) ∧
    lenT p i PP * (htCost Y.d.l₂ (bndB (uPrime (dat p i) u1) g) * l1 (uPrime (dat p i) u1)) ≤ C * unitE p

end Steps

def Short : Prop := Covers fun _ _ _ _ p i Y PP C => ∀ u1, Quo p i PP u1 → ShortAt p i Y PP C u1

def Geom : Prop := Covers fun _ _ _ _ p i Y PP _ => ∀ u1, Quo p i PP u1 → GeomAt p i Y u1

def MultC : Prop := Covers fun _ _ _ _ p i Y PP C => ∀ u1, Quo p i PP u1 → MultAt p i Y PP C u1

def Budget : Prop := Covers fun _ _ _ _ p i Y PP C => ∀ u1, Quo p i PP u1 → BudgetAt p i Y PP C u1

end GlobalTheory.CovHt

end
