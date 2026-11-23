import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.QuasiReflectionEqMulTransvectionsOfHyperbolicPla
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermHyperbolic
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiReflection_eq_mul_transvections_of_hyperbolicPlane : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), IsHerm σ G → ∀ (x z : Fin n → E) (a u : E), hf σ G z z = 0 → hf σ G x z ≠ 0 → hf σ G x x ≠ 0 → hf σ G (x + a • z) (x + a • z) ≠ 0 → u * σ u = 1 → ∃ m ∈ TvGen σ G, tv σ G x ((u - 1) / hf σ G x x) = m * tv σ G (x + a • z) ((u - 1) / hf σ G (x + a • z) (x + a • z)) := by
  first | exact @GlobalTheory.UTrans.PlaneRefl.quasiRefl_eq_mul_of_plane | exact GlobalTheory.UTrans.PlaneRefl.quasiRefl_eq_mul_of_plane | (intros; apply GlobalTheory.UTrans.PlaneRefl.quasiRefl_eq_mul_of_plane <;> assumption)
