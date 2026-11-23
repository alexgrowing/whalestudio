import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSpanEigenOfBaseChangeEigen
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_eigen_of_baseChange_eigen' : ∀ (l : ℕ) [Fact l.Prime] (M S : Type) [AddCommGroup M] [Module ℤ_[l] M] (B : Submodule ℤ_[l] M) [Module.Free ℤ_[l] B]
  (g : S → Module.End ℤ_[l] M) (χ : S → ℤ_[l]), (∀ s, ∀ b ∈ B, g s b ∈ B) →
  ∀ x ∈ LinearMap.range (LinearMap.baseChange (PadicAlgCl l) B.subtype),
  (∀ s, LinearMap.baseChange (PadicAlgCl l) (g s) x = algebraMap ℤ_[l] (PadicAlgCl l) (χ s) • x) →
  x ∈ Submodule.span (PadicAlgCl l) {y | ∃ b ∈ B, (∀ s, g s b = χ s • b) ∧ y = (1 : PadicAlgCl l) ⊗ₜ[ℤ_[l]] b} := by
  first | exact @GlobalTheory.mem_span_eigen_of_baseChange_eigen | exact GlobalTheory.mem_span_eigen_of_baseChange_eigen | (intros; apply GlobalTheory.mem_span_eigen_of_baseChange_eigen <;> assumption)
