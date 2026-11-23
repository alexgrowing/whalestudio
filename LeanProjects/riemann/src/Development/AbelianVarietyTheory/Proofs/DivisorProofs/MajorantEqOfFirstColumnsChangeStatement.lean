import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajorantEqOfFirstColumnsChange
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartBottomLeftBlock
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.ChartGraph
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.majorant_eq_of_firstColumns_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x' y : Frame X.Ψ r)
    (τ : X.Ψ) (C : Matrix (Fin X.p0) (Fin X.p0) ℂ), C.det ≠ 0 → (X.gramPos y τ).det ≠ 0 →
    (∀ a : Fin X.p0, col (mat x' τ) (Fin.castLE X.p0_le a) =
      ∑ c : Fin X.p0, C c a • col (mat y τ) (Fin.castLE X.p0_le c)) →
    ∀ v : Fin r → ℂ, X.maj x' τ v = X.maj y τ v := by
  first | exact @GlobalTheory.MajCols.maj_eq_of_cols | exact GlobalTheory.MajCols.maj_eq_of_cols | (intros; apply GlobalTheory.MajCols.maj_eq_of_cols <;> assumption)
