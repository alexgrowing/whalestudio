import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpCStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PositiveSpanMatrices
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.FundamentalSetFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormBcharMulNfacRmul
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames

namespace GlobalTheory.PoincareSeriesCompare

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open MeasureTheory Topology
open GlobalTheory.IndefiniteRowSideFullHecke.FundamentalSetFrames (GapsNonneg pairing IsInvWeight wsq normSq ATilde fundSq IsExt idFrame flagBall
  ballSup term PoincareStatement CuspidalStatement PoincareCuspidalStatement)
open scoped ENNReal NNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem nonempty_type (X : Data E r) : Nonempty X.Ψ := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  by_cases h : τ ∈ X.Ψ
  · exact ⟨⟨τ, h⟩⟩
  · exact ⟨⟨_, not_not.mp (mt (X.cmType τ).mpr h)⟩⟩

theorem isOrth_x0F (X : Data E r) : IsOrth X (x0F X) := fun τ => (X.signature τ).choose_spec.2

theorem not_isIso_of_definite (X : Data E r) (h : X.p0 = 0 ∨ X.p0 = r) (ξ : Fin r → E) :
    ¬ X.IsIso ξ := by
  rintro ⟨-, h0, hne⟩
  obtain ⟨τ⟩ := nonempty_type X
  have hx : X.IsOrtho (x0F X) := isOrth_x0F X
  have hdet : (mat (x0F X) τ).det ≠ 0 := (X.signature τ).choose_spec.1
  set y : Fin r → ℂ := Data.emb τ.1 ξ with hy
  have hyy : hermC τ.1 X.Gm y y = 0 := by rw [hy, hermC_emb, h0, map_zero]
  have hre := PositiveSpanMatrices.re_self X hx τ hdet y
  rw [hyy, Complex.zero_re] at hre
  have hsq : ∑ c : Fin r, ‖hermC τ.1 X.Gm y (col (mat (x0F X) τ) c)‖ ^ 2 = 0 := by
    rcases h with h | h
    · have hs : ∀ c : Fin r, sgn X.p0 (c : ℕ) = -1 := fun c => by simp [sgn, h]
      simp only [hs, neg_one_mul, Finset.sum_neg_distrib] at hre
      linarith
    · have hs : ∀ c : Fin r, sgn X.p0 (c : ℕ) = 1 := fun c => by simp [sgn, h, c.isLt]
      simp only [hs, one_mul] at hre
      linarith
  have hall : ∀ c, hermC τ.1 X.Gm y (col (mat (x0F X) τ) c) = 0 := by
    intro c
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun c _ =>
      sq_nonneg ‖hermC τ.1 X.Gm y (col (mat (x0F X) τ) c)‖)).mp hsq c (Finset.mem_univ c)
    simpa using this
  have hy0 : y = 0 := by
    rw [PositiveSpanMatrices.expand X hx τ hdet y]
    simp [hall]
  apply hne
  funext a
  have : τ.1 (ξ a) = 0 := congrFun hy0 a
  exact (map_eq_zero τ.1).mp this

def CuspAllGapsStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (τ0 : X.Ψ), 0 < X.p0 → X.p0 < r →
    (∀ τ : X.Ψ, ∀ i j : Fin r, (j : ℕ) = i + 1 → (j : ℕ) ≠ X.p0 → la τ j ≤ la τ i) →
    (∀ i0 i1 : Fin r, (i0 : ℕ) = 0 → (i1 : ℕ) = r - 1 → la τ0 i0 < la τ0 i1) →
    ∀ P, X.IsBddSec la P → P ∈ X.SS la

def Matches (X : Data E r) (la : Wt X.Ψ r) (W : Frame X.Ψ r → ℝ≥0∞) (u : Frame X.Ψ r → EReal) : Prop :=
  ∀ x ∈ X.dom, W x = EReal.exp (-((phla X la x : EReal) + u x))

def PoincarePointwiseStatement : Prop :=
  ∀ (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 →
  ∀ bb : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb → ∀ la : Wt X.Ψ r,
    ∀ u, IsInvWeight X u → ∀ F ∈ ATilde X x0 bb la u, ∀ P, IsExt X x0 la F P →
      (∀ x ∈ X.dom, Summable fun γ : X.Γ => ‖term X la P γ x‖) ∧ X.IsBddSec la (poin X la P) ∧
      (∀ FF, GlobalTheory.IndefiniteRowSideFullHecke.FundamentalSetFrames.IsFundSet X x0 FF → fundSq X x0 la u FF (poin X la P) < ⊤) ∧
      (∀ ε : ℝ, 0 < ε → ∃ C : ℝ≥0, ∀ y ∈ X.dom,
        ENNReal.ofReal (X.pnorm la (poin X la P) y) ≤ C * ballSup X ε u y) ∧
      ∀ (la' : Wt X.Ψ r) (g : Frame X.Ψ r → ℂ), X.IsSec la' g →
        ∀ x ∈ X.dom, poin X (la' + la) (g * P) x = g x * poin X la P x

end

end GlobalTheory.PoincareSeriesCompare
