import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisBoundedModuleValuationRingPi
import Mathlib
open IsDedekindDomain NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_bounded_module_valuationRing_pi : ∀ {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F)) (d : ℕ) (M : Set (Fin d → F)), (0 : Fin d → F) ∈ M → (∀ x ∈ M, ∀ y ∈ M, x + y ∈ M) → (∀ a : F, p.valuation F a ≤ 1 → ∀ x ∈ M, a • x ∈ M) → (∀ i, Pi.single i 1 ∈ M) → (∃ D : F, D ≠ 0 ∧ ∀ x ∈ M, ∀ i, p.valuation F (D * x i) ≤ 1) → ∃ (m : ℕ) (b : Fin m → Fin d → F), (∀ k, b k ∈ M) ∧ (∀ x ∈ M, ∃ a : Fin m → F, (∀ k, p.valuation F (a k) ≤ 1) ∧ x = ∑ k, a k • b k) ∧ LinearIndependent F b := by
  first | exact @GlobalTheory.locBasis_of_bounded | exact GlobalTheory.locBasis_of_bounded | (intros; apply GlobalTheory.locBasis_of_bounded <;> assumption)
