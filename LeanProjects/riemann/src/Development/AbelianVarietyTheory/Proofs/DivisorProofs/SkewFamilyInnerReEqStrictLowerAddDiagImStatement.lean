import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewFamilyInnerReEqStrictLowerAddDiagIm
import Mathlib
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skew_family_inner_re_eq_strictLower_add_diagIm : ∀ {ι : Type} [Fintype ι] {r : ℕ} (s : Fin r → ℝ), (∀ a, s a * s a = 1) → ∀ (Y Y' : ι × Fin r × Fin r → ℂ), (∀ τ a b, Y (τ, b, a) = -((s a * s b : ℝ) : ℂ) * conj (Y (τ, a, b))) → (∀ τ a b, Y' (τ, b, a) = -((s a * s b : ℝ) : ℂ) * conj (Y' (τ, a, b))) → ∑ p, (conj (Y p) * Y' p).re = 2 * ∑ q : ι × {p : Fin r × Fin r // p.2 < p.1}, (conj (Y (q.1, q.2.1.1, q.2.1.2)) * Y' (q.1, q.2.1.1, q.2.1.2)).re + ∑ τ, ∑ a, (Y (τ, a, a)).im * (Y' (τ, a, a)).im := by
  first | exact @GlobalTheory.skew_family_inner_re_split | exact GlobalTheory.skew_family_inner_re_split | (intros; apply GlobalTheory.skew_family_inner_re_split <;> assumption)
