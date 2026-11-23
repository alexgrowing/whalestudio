import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicVectorRationalOrbit
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_vector_rational_orbit : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (X : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ r s : ℕ), B.IsGood σ → X.IsHerm σ B r s → H.IsAdapted σ B X X₁ j₀ j₁ → ∀ x : Fin n → E, x ≠ 0 → form σ X.J x x = 0 → ∃ γ ∈ ratU σ X.J, mat γ *ᵥ incV F x = incV F H.x := by
  first | exact @GlobalTheory.IsotropicWitt.exists_rat_unitary_isotropic | exact GlobalTheory.IsotropicWitt.exists_rat_unitary_isotropic | (intros; apply GlobalTheory.IsotropicWitt.exists_rat_unitary_isotropic <;> assumption)
