import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentHaarLeviConjMeasure
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
theorem _root_.GlobalTheory.T.unipotent_haar_levi_conj_measure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (Y : Spc F E n) (Y₁ : Spc F E n₁) (H : Plane E n n₁) (r s i₀ i₁ : ℕ), B.IsGood σ → Y.IsHerm σ B r s → H.IsAdapted σ B Y Y₁ i₀ i₁ → ∀ (t : (AE F E)ˣ) (m : UA σ Y.J), IsLevi (W₁ := Y₁) H (Units.map (cA σ : AE F E →* AE F E) t) 1 m → ∀ μN : Measure (unip σ Y H), μN.IsHaarMeasure → ∀ S : Set (unip σ Y H), ENNReal.ofReal ((absE F E t : ℝ) ^ ((n : ℝ) - 1)) * μN (Subtype.val ⁻¹' ((fun g => m⁻¹ * g * m) '' (Subtype.val '' S))) = μN S := by
  first | exact @GlobalTheory.LeviConjHaar.levi_conj_haar | exact GlobalTheory.LeviConjHaar.levi_conj_haar | (intros; apply GlobalTheory.LeviConjHaar.levi_conj_haar <;> assumption)
