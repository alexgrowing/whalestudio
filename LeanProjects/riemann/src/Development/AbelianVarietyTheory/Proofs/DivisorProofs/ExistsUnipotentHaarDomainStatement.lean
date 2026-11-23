import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentHaarDomain
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unipotent_haar_domain : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E d₁) (H' : Plane E n d₁) (i₀ i₁ r s r₁ s₁ : ℕ), B.IsGood σ → W.IsSkew σ B r s → W₁.IsSkew σ B r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → ∃ (μ : Measure (unip σ W H')) (𝓕 : Set (unip σ W H')), μ.IsHaarMeasure ∧ IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H')) 𝓕 μ ∧ μ 𝓕 = 1 := by
  first | exact @GlobalTheory.UnipHaar.exists_haar_fundamentalDomain_mass_one | exact GlobalTheory.UnipHaar.exists_haar_fundamentalDomain_mass_one | (intros; apply GlobalTheory.UnipHaar.exists_haar_fundamentalDomain_mass_one <;> assumption)
