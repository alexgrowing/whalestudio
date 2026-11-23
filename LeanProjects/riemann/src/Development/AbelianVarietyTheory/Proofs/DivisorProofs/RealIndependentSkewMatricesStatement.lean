import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealIndependentSkewMatrices
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
open NumberField Matrix ReciprocityTheory.ChartRestriction.G.FD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.real_independent_skew_matrices : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r n : ℕ} (G : Matrix (Fin r) (Fin r) E), G.det ≠ 0 → ∀ e : Fin n → Matrix (Fin r) (Fin r) E, (∀ i, (e i)ᵀ * G + G * (e i).map cc = 0) → LinearIndependent (maximalRealSubfield E) e → LinearIndependent E e := by
  first | exact @GlobalTheory.linearIndependent_of_skew_of_real | exact GlobalTheory.linearIndependent_of_skew_of_real | (intros; apply GlobalTheory.linearIndependent_of_skew_of_real <;> assumption)
