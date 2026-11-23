import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FiltrationCocycleLiftCriterion

noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions

section AtRecord

variable {D : D7} (L : SizeData₂ D)

def GamL : ℝ := Real.exp (L.CGam * (D.R.m : ℝ) ^ 5 * D.R.f * L.sc.L)

def ThickSetLowerBound (_L : SizeData₂ D) : Prop := D.host.secondSet_card_lower_bound

def ChTT_at : Prop :=
  L.sc.delta1 * D.R.n / 2 ≤ (D.host.TT.card : ℝ) ∧ (D.host.TT.card : ℝ) ≤ 2 * L.sc.delta1 * D.R.n

open Classical in

def largeOrderResiduePrimes : Finset ℕ :=
  (Finset.range ⌈L.sc.X'⌉₊).filter (fun p =>
    p.Prime ∧ G.IsResidueClassZero D p ∧ L.sc.x ^ (L.sc.eps / 4) ≤ (addOrderOf (G.hP D p) : ℝ))

variable {L}

open Classical in

def badTops (X : G.Inst D L) (p : ℕ) : Finset (G.HH D) :=
  D.host.TT.filter (fun t => ¬ G.Good X p (X.bs (G.stepP D p) t))

def ChBad_at (X : G.Inst D L) (Cb : ℝ) : Prop :=
  ∑ p ∈ largeOrderResiduePrimes L, Real.log p / p * ((badTops X p).card : ℝ) ≤
    4 * (Cb * L.sc.x ^ (-2 : ℝ)) * L.sc.delta1 * D.R.n * ∑ p ∈ largeOrderResiduePrimes L, Real.log p / p

def BoundsAtX (x eps C : ℝ) (f : ℕ → ℂ) (M : ℕ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), GlobalTheoryTheory.Induces χ f M →
    ‖GlobalTheoryTheory.gChi χ x‖ ≤ x ^ ((1 : ℝ) / 2 + eps) ∧ ‖GlobalTheoryTheory.logDerivativeAtOne χ‖ ≤ C * Real.log x

def ChQD_at (D : D7) (x eps C : ℝ) : Prop :=
  BoundsAtX x eps C (GlobalTheoryTheory.psDir D.host.q) (8 * D.host.q * D.host.d) ∧
  BoundsAtX x eps C (GlobalTheoryTheory.chDir D.host.d) (8 * D.host.q * D.host.d) ∧
  BoundsAtX x eps C (fun a => GlobalTheoryTheory.chDir D.host.d a * GlobalTheoryTheory.psDir D.host.q a) (8 * D.host.q * D.host.d)

def ChThin_at (D : D7) (x eps c : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), GlobalTheoryTheory.IsCharED D χ →
    ∀ y : ℝ, Real.exp (x ^ (eps / 3)) / 3 ≤ y → ‖GlobalTheoryTheory.gChi χ y‖ ≤ y * Real.exp (-(c * x ^ (eps / 8)))

variable (L)

def ChProviso_at (C0 : ℝ) : Prop :=
  ∀ u, C0⁻¹ ≤ (D.duS u : ℝ) * GamL L ^ 2 / D.what₂.Dstar ∧ (D.duS u : ℝ) * GamL L ^ 2 / D.what₂.Dstar ≤ C0

def ChCode_at (C0 CH : ℝ) : Prop :=
  C0 * GamL L ^ 2 * L.sc.x ^ CH ≤ (Fintype.card D.what₂.Word : ℝ)

end AtRecord

section Family

variable {eps : ℝ} (Fm : FamP eps)

def ThickSetEventually : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ThickSetLowerBound (Fm.L x i)

def ChosenTT : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ChTT_at (Fm.L x i)

def ChosenBad (Cb : ℝ) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ChBad_at (Fm.Gx x i) Cb

def ChosenQD (C5 : ℝ) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ChQD_at (Fm.D x i) x eps C5

def ChosenThin (c6 : ℝ) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ChThin_at (Fm.D x i) x eps c6

def ChosenProviso (C0 : ℝ) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ChProviso_at (Fm.L x i) C0

def ChosenCode (C0 CH : ℝ) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ChCode_at (Fm.L x i) C0 CH

def Chosen (CH C0 C5 c6 Cb : ℝ) : Prop :=
  ThickSetEventually Fm ∧ ChosenTT Fm ∧ ChosenBad Fm Cb ∧ ChosenQD Fm C5 ∧ ChosenThin Fm c6 ∧
    ChosenProviso Fm C0 ∧ ChosenCode Fm C0 CH

def ChosenE (C0 CH : ℝ) : Prop :=
  ∃ C5 c6 Cb : ℝ, 0 < C5 ∧ 0 < c6 ∧ 0 < Cb ∧ Chosen Fm CH C0 C5 c6 Cb

def ChosenEx (CH : ℝ) : Prop := ∃ C0 : ℝ, 1 ≤ C0 ∧ ChosenE Fm C0 CH

end Family

end Formalism.MainNotions

end
