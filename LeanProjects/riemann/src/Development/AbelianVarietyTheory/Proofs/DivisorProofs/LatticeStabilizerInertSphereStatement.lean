import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStabilizerInertSphere
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncMatTranspose
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_stabilizer_inert_sphere : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (r s : ℕ), X.IsHerm σ B r s →
    ∀ (m : ℕ) (x y : Fin m → Fin n → E), (∀ i, x i ∈ X.L ∧ y i ∈ X.L) → ∑ i, form σ X.J (x i) (y i) = 1 →
    ∀ (v : Pl F) (k : UA σ W.J), (∀ γ, γ * Matrix.transpose (mat k) ∈ latAtV X W v ↔ γ ∈ latAtV X W v) →
    ∀ z ∈ GlobalTheory.InertSph.latAt W v, mat k *ᵥ z ∈ GlobalTheory.InertSph.latAt W v ∧ mat k⁻¹ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v := by
  first | exact @GlobalTheory.LatStabTensor.latAt_stab | exact GlobalTheory.LatStabTensor.latAt_stab | (intros; apply GlobalTheory.LatStabTensor.latAt_stab <;> assumption)
