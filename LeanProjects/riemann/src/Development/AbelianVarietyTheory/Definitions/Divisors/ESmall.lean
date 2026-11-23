import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FactorDepthInertBounds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SplitQuadraticMinSums
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BigBlockCharacters
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.TypedPartSplitPrimes
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FactorDepth GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.IndefiniteRowSideFullHecke.SplitQuadraticRamification (IsBig sumSmallSpread)

namespace GlobalTheory.RefSum

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

open Classical in

def ExpBd (k : ℕ) (cx : Lt1 Dw → ℕ) (Mb Sm : ℝ) (M : ℕ) : Prop :=
  0 ≤ Mb ∧ (∀ τ : E →+* ℂ, ((∑ f ∈ Finset.univ.filter (fun f : Lt1 Dw => IsBig k f ∧ f.1 = τ), cx f : ℕ) : ℝ) ≤ Mb) ∧
    (sumSmallSpread k cx : ℝ) ≤ Sm ∧ ∀ f, cx f ≤ M

def Shape (F k m : ℕ) : Prop :=
  Dw.p + Dw.q + 1 = k + m ∧ Dw.q ≤ m ∧ m ≤ k ∧ 1 ≤ m ∧ 2 ≤ k ∧ Module.finrank ℚ E = 2 * F

def WtBd (k n : ℕ) (u : Weight Dw) (B : ℕ) (Sg : ℝ) : Prop :=
  (∀ τ, Antitone (u τ)) ∧ (∀ τ (i : Fin (Dw.p + Dw.q)), (i : ℕ) + 2 = k → u τ i = 0) ∧
    (∀ τ (i j : Fin (Dw.p + Dw.q)), (i : ℕ) + 1 = Dw.p → (j : ℕ) = Dw.p → (n : ℤ) + 1 ≤ u τ i - u τ j) ∧
    (∀ τ i, |u τ i| ≤ B) ∧
    ∀ τ, (∑ i ∈ Finset.univ.filter (fun i : Fin (Dw.p + Dw.q) => (i : ℕ) + 2 < k), (u τ i : ℝ)) ≤ Sg

end Free

def eSmall (F N m : ℕ) (Mb Sm : ℝ) (M p : ℕ) : ℝ :=
  (F * m * Mb * (4 + Real.logb p M / 2) + Sm) / ((p : ℝ) - 1) + F * (m + 1) * (N : ℝ) ^ 2 * (Real.logb p M + 1)

open Classical in

def eOf (F N k m : ℕ) (Mb Sm : ℝ) (vd : ℕ → ℝ) (M : ℕ) (S R : Finset ℕ) (p : ℕ) : ℝ :=
  if M < p then 0 else if p ∈ S then F * m * (1 + vd p / 2) * Mb + Sm
  else if p ∈ R then (F * N * Mb + Sm) / ((p : ℝ) - 1)
  else if m * p < k then eSmall F N m Mb Sm M p + 1 else (6 * F * m * Mb + Sm) / ((p : ℝ) - 1) + 1

example (F N k m : ℕ) (Mb Sm : ℝ) (vd : ℕ → ℝ) (S R : Finset ℕ) : eOf F N k m Mb Sm vd 3 S R 5 = 0 := by simp [eOf]

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

def WtAt (PP C : ℝ) (u1 : Weight (dat p i)) : Prop :=
  Shape (dat p i) D.R.f D.R.k D.R.m ∧ D.R.k ≤ (dat p i).p + 1 ∧ ∃ (B : ℕ) (Sg : ℝ), WtBd (dat p i) D.R.k (nCol (dat p i)) u1 B Sg ∧
    lenT p i PP * ((B : ℝ) + 1) ≤ C * L.sc.b ∧ lenT p i PP * Sg ≤ C * L.sc.b ∧ 1 ≤ lenT p i PP

def NumAt (PP C : ℝ) : Prop :=
  1 ≤ L.sc.L ∧ 1 ≤ L.sc.b ∧ Real.log L.sc.b ≤ C * L.sc.L ∧ 1 ≤ Real.log (Real.log L.sc.x) ∧
    D.R.f * D.R.m * L.sc.b * L.sc.L * Real.log (Real.log L.sc.x) ≤ C * unitE p ∧
    Real.log (Real.log D.R.k) ≤ C * Real.log (Real.log L.sc.x) ∧ Real.log D.R.r ≤ C * L.sc.L ∧ Formalism.MainNotions.DIV.Cons.vd2 D ≤ C * L.sc.L ∧
    lenT p i PP * (D.R.r : ℝ) ^ 3 ≤ C * L.sc.b ∧
    ∀ q ∈ ({D.host.q, D.host.d} : Finset ℕ), D.R.r * Real.log q / ((q : ℝ) - 1) ≤ C * D.R.m * L.sc.L

end Point

def WtPt : Prop := Lifts fun Fm x _ ι p i PP C => (i : ℕ) + 1 < (Fm.D x ι).R.m → ∀ u1, Quo p i PP u1 → WtAt p i PP C u1

def NumPt : Prop := Lifts fun Fm x _ ι p i PP C => (i : ℕ) + 1 < (Fm.D x ι).R.m → NumAt p i PP C

end GlobalTheory.RefSum

end
