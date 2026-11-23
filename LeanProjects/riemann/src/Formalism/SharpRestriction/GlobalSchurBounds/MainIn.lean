import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FiltrationBoundaryCriterion
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FiltrationCocycleLiftCriterion
import Formalism.SharpRestriction.GlobalSchurBounds.Chosen

noncomputable section

namespace Formalism.MainNotions

open Formalism.BasicNotions

def GoodAllFor (Q : ℝ) (f : ℕ → ℂ) (M : ℕ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), GlobalTheoryTheory.Induces χ f M → GlobalTheoryTheory.GoodFor Q χ

def Boxes_at (D : D7) (x eps : ℝ) : Prop :=
  GoodAllFor (8 * GlobalTheoryTheory.X1 x eps) (GlobalTheoryTheory.psDir D.host.q) (8 * D.host.q * D.host.d) ∧
  GoodAllFor (8 * GlobalTheoryTheory.X1 x eps) (fun a => GlobalTheoryTheory.chi8 a * GlobalTheoryTheory.psDir D.host.q a) (8 * D.host.q * D.host.d) ∧
  GoodAllFor (8 * GlobalTheoryTheory.X1 x eps * GlobalTheoryTheory.X2 x eps) (GlobalTheoryTheory.chDir D.host.d) (8 * D.host.q * D.host.d) ∧
  GoodAllFor (8 * GlobalTheoryTheory.X1 x eps * GlobalTheoryTheory.X2 x eps) (fun a => GlobalTheoryTheory.chi8 a * GlobalTheoryTheory.chDir D.host.d a)
    (8 * D.host.q * D.host.d) ∧
  GoodAllFor (8 * GlobalTheoryTheory.X1 x eps * GlobalTheoryTheory.X2 x eps) (fun a => GlobalTheoryTheory.chDir D.host.d a * GlobalTheoryTheory.psDir D.host.q a)
    (8 * D.host.q * D.host.d) ∧
  GoodAllFor (8 * GlobalTheoryTheory.X1 x eps * GlobalTheoryTheory.X2 x eps)
    (fun a => GlobalTheoryTheory.chi8 a * GlobalTheoryTheory.chDir D.host.d a * GlobalTheoryTheory.psDir D.host.q a) (8 * D.host.q * D.host.d)

def BoxesF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ Y : ℝ, (x ^ (1 / Fm.J) ≤ Y ∧ Y ≤ x) ∧
    Boxes_at (Fm.D x i) Y eps ∧ GlobalTheoryTheory.BoxE (Fm.D x i) Y eps

def QDRows_at (D : D7) (x eps : ℝ) : Prop :=
  D.host.q.Prime ∧ D.host.q % 8 = 3 ∧ Real.sqrt (GlobalTheoryTheory.X1 x eps) < D.host.q ∧ (D.host.q : ℝ) ≤ GlobalTheoryTheory.X1 x eps ∧
  D.host.d.Prime ∧ D.host.d % 16 = 7 ∧ Real.sqrt (GlobalTheoryTheory.X2 x eps) < D.host.d ∧ (D.host.d : ℝ) ≤ GlobalTheoryTheory.X2 x eps ∧
  GlobalTheoryTheory.kronSym (-(D.host.d : ℤ)) D.host.q = 1 ∧
  (∀ p : ℕ, p.Prime → (p : ℝ) ≤ x ^ (eps / 5) → GlobalTheoryTheory.kronSym (-(D.host.d : ℤ)) p = 1) ∧
  Real.log (D.host.QS * D.host.q * D.host.d) ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2

def QDRowsF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, ∃ Y : ℝ, (x ^ (1 / Fm.J) ≤ Y ∧ Y ≤ x) ∧ QDRows_at (Fm.D x i) Y eps

def TR_at (D : D7) : Prop :=
  ∃ V : D.what₂.EE ≃ₗᵢ[ℂ] D.what₂.EE, ∀ u, ∃ a : ℂ, a ≠ 0 ∧
    ∃ U : D.what₂.Mu u ≃ₗᵢ[ℂ] D.what₂.Mu u, ∀ φ F, D.what₂.Bu u φ F = a * D.besS u (U φ) (V F)

def TRF {eps : ℝ} (Fm : FamP eps) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, TR_at (Fm.D x i)

def SB_at {D : D7} (L : SizeData₂ D) (CH : ℝ) : Prop :=
  sFrame D.div.Nu D.div.h + D.div.RR.muMax ≤ L.sc.x ^ CH * L.sc.b

def SBF {eps : ℝ} (Fm : FamP eps) (CH : ℝ) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, SB_at (Fm.L x i) CH

def MinkMult (n M : ℕ) : Prop :=
  ∀ H : Subgroup (Matrix.GeneralLinearGroup (Fin n) ℚ), Finite H → Nat.card H ∣ M

def MinkLit (C : ℝ) : Prop :=
  ∀ n : ℕ, 2 ≤ n → ∃ M : ℕ, 0 < M ∧ MinkMult n M ∧ Real.log (M : ℝ) ≤ C * n * Real.log n

def DGamChoice_at (D : D7) : Prop :=
  ∀ M : ℕ, MinkMult (2 * D.R.f * D.R.N D.R.m) M → ∀ u, (D.mem u).C.DGam ∣ M

def DGamChoiceF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, DGamChoice_at (Fm.D x i)

end Formalism.MainNotions

end
