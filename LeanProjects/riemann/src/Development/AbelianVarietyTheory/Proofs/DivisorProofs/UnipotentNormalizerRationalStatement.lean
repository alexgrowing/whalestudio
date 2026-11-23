import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentNormalizerRational
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalDomainClosure

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_normalizer_rational : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁) (r s i₀ i₁ : ℕ), Y.IsHerm σ B r s → H.IsAdapted σ B Y Y₁ i₀ i₁ → ∀ (t : (AE F E)ˣ) (m : UA σ Y.J), IsLevi (W₁ := Y₁) H t 1 m → ∀ q ∈ ratU σ Y.J ⊓ Subgroup.closure {g : UA σ Y.J | mat g *ᵥ incV F H.x = incV F H.x}, (∀ u ∈ unip σ Y H, q * u * q⁻¹ ∈ unip σ Y H) ∧ m⁻¹ * q * m * q⁻¹ ∈ unip σ Y H := by
  first | exact @GlobalTheory.StabNormal.stab_normalises_unip | exact GlobalTheory.StabNormal.stab_normalises_unip | (intros; apply GlobalTheory.StabNormal.stab_normalises_unip <;> assumption)
