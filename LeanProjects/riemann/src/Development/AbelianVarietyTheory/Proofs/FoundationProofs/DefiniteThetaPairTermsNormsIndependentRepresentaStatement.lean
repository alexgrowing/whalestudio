import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresenta
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteThetaPair_terms_norms_independent_representatives : ∀ (D : D7), Inp D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (t0 : ℂ) (Q : ℕ), Crv D cc δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → ∀ (P : Pair D cc δ t0 Q), 0 < Q → (∀ γ ∈ ratG D P.a, ∀ k ∈ intG D P.a, ∀ x h T, P.term (γ * x * k) h T = P.term x h T) ∧ (∀ γ ∈ ratG D P.d, ∀ j ∈ P.J, ∀ h, P.sq (γ * h * j) = P.sq h) ∧ (∀ (s : Cls D P.a (intG D P.a) → GA D P.a), (∀ q, DoubleCoset.mk (ratG D P.a) (intG D P.a) (s q) = q) → ∀ h T, P.coord h T = ∑ᶠ q, ((gam D (intG D P.a) (s q) : ℂ))⁻¹ * P.term (s q) h T) ∧ (∀ (s : Cls D P.d P.J → GA D P.d), (∀ q, DoubleCoset.mk (ratG D P.d) P.J (s q) = q) → P.norm = ∑ᶠ q, ((gam D P.J (s q) : ℝ))⁻¹ * P.sq (s q)) ∧ ((∃ h T, P.coord h T ≠ 0) → 0 < P.norm) := by
  first | exact @GlobalTheory.NormSum.RepInv.rep_indep | exact GlobalTheory.NormSum.RepInv.rep_indep | (intros; apply GlobalTheory.NormSum.RepInv.rep_indep <;> assumption)
