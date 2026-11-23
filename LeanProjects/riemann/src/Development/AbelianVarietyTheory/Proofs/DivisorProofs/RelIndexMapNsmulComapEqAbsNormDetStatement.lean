import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexMapNsmulComapEqAbsNormDet
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_map_nsmul_comap_eq_abs_norm_pow_mul_det : ∀ (E Γ : Type) [Field E] [NumberField E] [AddCommGroup Γ] [Module E Γ] [FiniteDimensional E Γ] (A : AddSubgroup Γ), A.FG → (∀ x : Γ, ∃ N : ℕ, 0 < N ∧ N • x ∈ A) → ∀ (m : Module.End E Γ) (N : ℕ), N ≠ 0 → LinearMap.det m ≠ 0 → (∀ x ∈ A, N • m x ∈ A) → (((A.map (N • AddMonoidHom.id Γ)).relIndex (A.comap m.toAddMonoidHom) : ℕ) : ℚ) = |Algebra.norm ℚ ((N : E) ^ Module.finrank E Γ * LinearMap.det m)| := by
  first | exact @GlobalTheory.relIndex_map_nsmul_comap_eq_abs_norm_det | exact GlobalTheory.relIndex_map_nsmul_comap_eq_abs_norm_det | (intros; apply GlobalTheory.relIndex_map_nsmul_comap_eq_abs_norm_det <;> assumption)
