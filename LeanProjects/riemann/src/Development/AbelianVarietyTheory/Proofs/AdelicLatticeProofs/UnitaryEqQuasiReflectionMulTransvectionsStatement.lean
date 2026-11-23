import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryEqQuasiReflectionMulTransvections
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermHyperbolic
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_eq_quasiReflection_mul_transvections : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHerm (c : E →+* E) G → (∃ z : Fin n → E, z ≠ 0 ∧ hf (c : E →+* E) G z z = 0) → ∀ γ, IsU (c : E →+* E) G γ → (∀ x, hf (c : E →+* E) G x x ≠ 0 → ∃ m ∈ TvGen (c : E →+* E) G, γ = tv (c : E →+* E) G x ((γ.det - 1) / hf (c : E →+* E) G x x) * m) ∧ (γ.det = 1 → γ ∈ TvGen (c : E →+* E) G) := by
  first | exact @GlobalTheory.UTrans.isU_eq_tv_mul_tvGen | exact GlobalTheory.UTrans.isU_eq_tv_mul_tvGen | (intros; apply GlobalTheory.UTrans.isU_eq_tv_mul_tvGen <;> assumption)
