import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilMatrixTransportSchwartz
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsWeilCharacterDetEqAbsDetPowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergPreservesSchwartzBStatement
open MeasureTheory Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_matrix_transport_schwartz : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n d : ℕ} (ψ0 : AddChar k ℂ), Continuous ψ0 → ψ0 ≠ 1 →
    ∀ (ι : ((Fin d × Fin n → k) → ℂ) →ₗ[ℂ] (Matrix (Fin d) (Fin n) k → ℂ)),
    Set.BijOn ι (GlobalTheory.WeilM.SB (Fin d × Fin n → k) : Set _) (GlobalTheory.WeilM.SB (Matrix (Fin d) (Fin n) k) : Set _) →
    ∀ (Tr : Matrix (Fin d) (Fin n) k → ((Fin d × Fin n → k) → ℂ) → (Fin d × Fin n → k) → ℂ)
      (Mu : (Matrix (Fin d) (Fin n) k →ₗ[k] k) → ((Fin d × Fin n → k) → ℂ) → (Fin d × Fin n → k) → ℂ),
    (∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, Tr C φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Tr C φ) = fun Y => ι φ (Y + C)) →
    (∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, Mu l φ ∈ GlobalTheory.WeilM.SB _ ∧ ι (Mu l φ) = fun Y => ψ0 (l Y) * ι φ Y) →
    (∀ μ : @MeasureTheory.Measure (Fin d × Fin n → k) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ C, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Tr C φ y * (starRingEnd ℂ) (Tr C φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ) →
    (∀ μ : @MeasureTheory.Measure (Fin d × Fin n → k) (borel _), @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∀ l, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ φ' ∈ GlobalTheory.WeilM.SB _,
        ∫ y, Mu l φ y * (starRingEnd ℂ) (Mu l φ' y) ∂μ = ∫ y, φ y * (starRingEnd ℂ) (φ' y) ∂μ) →
    ∀ (S : GL (Fin n) k → ((Fin d × Fin n → k) → ℂ) → (Fin d × Fin n → k) → ℂ),
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, S g φ ∈ GlobalTheory.WeilM.SB _) →
    (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ∀ μ : @MeasureTheory.Measure (Fin d × Fin n → k) (borel _),
      @MeasureTheory.Measure.IsAddHaarMeasure _ _ _ (borel _) μ → ∫⁻ y, ‖S g φ y‖ₑ ^ 2 ∂μ = ∫⁻ y, ‖φ y‖ₑ ^ 2 ∂μ) →
    ∀ χ : kˣ →* ℂˣ, (∀ g, ∀ φ ∈ GlobalTheory.WeilM.SB _, ι (S g φ) = fun Y => (χ (Matrix.GeneralLinearGroup.det g) : ℂ) * ι φ (Y * g.val)) →
    ∃ ν : kˣ →* ℂˣ, (∀ x, ‖(ν x : ℂ)‖ = 1) ∧ ∀ g : GL (Fin n) k,
      (χ (Matrix.GeneralLinearGroup.det g) : ℂ) = ν (Matrix.GeneralLinearGroup.det g) * GlobalTheory.SplitFlip.apow (Matrix.GeneralLinearGroup.det g) ((d : ℂ) / 2) := by
  first | exact @GlobalTheory.HeisUnitRight.exists_unitary_factor_right | exact GlobalTheory.HeisUnitRight.exists_unitary_factor_right | (intros; apply GlobalTheory.HeisUnitRight.exists_unitary_factor_right <;> assumption)
