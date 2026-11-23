import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundDomUnipAdapted
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unip_fundamentalDomain_finite_pos_measure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n n₁ : ℕ) (X Y : Spc F E n) (X₁ : Spc F E n₁) (H : Plane E n n₁) (r s i₀ i₁ : ℕ), B.IsGood σ → X.IsHerm σ B r s → (reS X Y).IsHerm σ B r s → H.IsAdapted σ B (reS X Y) X₁ i₀ i₁ → ∀ μN : Measure (unip σ X H), μN.IsHaarMeasure → ∃ 𝓕 : Set (unip σ X H), IsFundamentalDomain ((ratU σ X.J).subgroupOf (unip σ X H)) 𝓕 μN ∧ μN 𝓕 ≠ 0 ∧ μN 𝓕 ≠ ⊤ := by
  first | exact @GlobalTheory.UnipMassAdapted.exists_fundDom_unip_adapted | exact GlobalTheory.UnipMassAdapted.exists_fundDom_unip_adapted | (intros; apply GlobalTheory.UnipMassAdapted.exists_fundDom_unip_adapted <;> assumption)
