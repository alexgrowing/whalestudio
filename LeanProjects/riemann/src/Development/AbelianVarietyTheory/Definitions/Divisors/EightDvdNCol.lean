import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Definitions.Foundations.NonnegOfMemCStarSet

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FactorDepth GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop

namespace GlobalTheory.RefSum

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) {c : Coeff l} {p : ℕ} [Fact p.Prime]

def FacBetween (la : PointsOfFlagModel.abelian₂ p c) (f : Lt1 Dw) (k : ℕ) (A B : ℝ) : Prop :=
  letI := H.starRing
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ y : IntFr Xo c T io,
    (A : EReal) ≤ nuFac p y f k ∧ (y.IsAlg → nuFac p y f k ≤ (B : EReal))

def NuBetween (la : PointsOfFlagModel.abelian₂ p c) (cx : Lt1 Dw → ℕ) (A B : ℝ) : Prop :=
  letI := H.starRing
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ y : IntFr Xo c T io,
    (A : EReal) ≤ nuP p y cx ∧ (y.IsAlg → nuP p y cx ≤ (B : EReal))

variable (c p) in

def OscLe (cx : Lt1 Dw → ℕ) (b : ℝ) : Prop :=
  ∀ la : PointsOfFlagModel.abelian₂ p c, ∃ A : ℕ, NuBetween Xo la cx A (A + b)

variable (Dw) in

def nCol : ℕ := 8 * ((∑ f : Lt1 Dw, 2 * rk f) / 8 + Fintype.card (Lt1 Dw) + 1)

variable (Dw) in

def shift (u : Weight Dw) (n : ℕ) (τ : Psi H) : ℤ :=
  ((n / 2 : ℕ) : ℤ) + 1 - if h : 0 < Dw.p then u τ ⟨Dw.p - 1, by omega⟩ else 0

variable (Dw) in

def thA (u : Weight Dw) (n : ℕ) : (E →+* ℂ) × ℕ → ℕ :=
  fun x => ((wtOf Dw (u + GlobalTheory.FlatLine.parWt Dw (shift Dw u n)) ((n / 2 : ℕ) : ℤ)).1 x).toNat

theorem eight_dvd_nCol : 8 ∣ nCol Dw := Dvd.intro _ rfl

theorem sum_le_nCol : ∑ f : Lt1 Dw, 2 * rk f ≤ nCol Dw := by
  unfold nCol; omega

theorem OscLe.mono {cx : Lt1 Dw → ℕ} {b b' : ℝ} (h : OscLe Xo c p cx b) (hb : b ≤ b') : OscLe Xo c p cx b' := fun la => by
  obtain ⟨A, hA⟩ := h la
  exact ⟨A, fun T io e ho y => ⟨(hA T io e ho y).1, fun ha => ((hA T io e ho y).2 ha).trans
    (EReal.coe_le_coe_iff.2 (by linarith))⟩⟩

def PrimeSum (S : Finset ℕ) (e : ℕ → ℝ) (s : ℝ) : Prop :=
  (∀ q ∈ S, q.Prime) ∧ (∀ q, 0 ≤ e q) ∧ (∀ q ∉ S, e q = 0) ∧ ∑ q ∈ S, e q * Real.log q ≤ s

example : PrimeSum ∅ 0 0 := ⟨by simp, fun _ => le_rfl, fun _ _ => rfl, by simp⟩

end Free

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

abbrev aOf (u1 : Weight (dat p i)) : (D.host.E →+* ℂ) × ℕ → ℕ := thA (dat p i) u1 (nCol (dat p i))

abbrev GOf (u1 : Weight (dat p i)) : WTZ D.host.E := wtZ (aOf p i u1) (nCol (dat p i))

def SumAt (PP C : ℝ) (u1 : Weight (dat p i)) : Prop :=
  ∃ (S : Finset ℕ) (e : ℕ → ℝ) (s : ℝ), PrimeSum S e s ∧ lenT p i PP * s ≤ C * unitE p ∧
    ∀ (q : ℕ) [Fact q.Prime], (∀ k, q ≠ D.host.g k) →
      OscLe (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c q (gap (dat p i) (aOf p i u1)) (e q)

def RefAt {l : Level p.T.Q.H} {Xo : Moduli (dat p i) l} {c : Coeff l} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r)
    (G : WTZ D.host.E) (PP C : ℝ) : Prop :=
  ∃ (S : Finset ℕ) (e : ℕ → ℝ) (s : ℝ), PrimeSum S e s ∧ lenT p i PP * s ≤ C * unitE p ∧
    ∀ q : ℕ, q.Prime → refExp_vp U (1 / 2500) G q ≤ (e q : EReal)

end Point

def SumPt : Prop := Lifts fun Fm x _ ι p i PP C => (i : ℕ) + 1 < (Fm.D x ι).R.m → ∀ u1, Quo p i PP u1 → SumAt p i PP C u1

def RefCore : Prop := Lifts fun Fm x _ ι p i PP C => (i : ℕ) + 1 < (Fm.D x ι).R.m → ∀ u1, Quo p i PP u1 →
  RefAt p i (p.T.U ((i : ℕ) + 1)) (GOf p i u1) PP C

def RefTheta : Prop := Covers fun _ _ _ _ p i Y PP C => ∀ u1, Quo p i PP u1 → RefAt p i Y.U (GOf p i u1) PP C

def RefW : Prop := Covers fun _ _ _ _ p i Y PP C => ∀ u1, Quo p i PP u1 → RefAt p i Y.U (wtOf (dat p i) u1 0) PP C

end GlobalTheory.RefSum

end
