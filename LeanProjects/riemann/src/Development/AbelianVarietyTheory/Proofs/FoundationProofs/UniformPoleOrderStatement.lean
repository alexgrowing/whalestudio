import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UniformPoleOrder
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_Lv_of_invariant_Gamma_of_forall_QAll : ∀ (E : Subring ℂ) (M : ℕ) (f : ℍ → ℂ), 0 < M → (∀ γ ∈ CongruenceSubgroup.Gamma M, ∀ τ : ℍ, f (γ • τ) = f τ) → (∀ γ : SL(2, ℤ), ∃ w : ℕ, QAll (· ∈ E) M fun τ => DD τ ^ w * f (γ • τ)) → ∃ w : ℕ, Lv E M w f := by
  first | exact @GlobalTheory.FN.uniform_pole_order | exact GlobalTheory.FN.uniform_pole_order | (intros; apply GlobalTheory.FN.uniform_pole_order <;> assumption)
