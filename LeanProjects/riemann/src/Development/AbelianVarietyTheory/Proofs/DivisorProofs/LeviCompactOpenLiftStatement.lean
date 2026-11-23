import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviCompactOpenLift
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_compact_open_lift : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r s r₁ s₁ : ℕ),
    B.IsGood σ → W.IsSkew σ B r s → W₁.IsSkew σ B r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (v : Pl F), ∀ k₁ ∈ KAt σ W₁ v, ∃ m ∈ KAt σ W v, IsLevi (W₁ := W₁) H' 1 k₁ m := by
  first | exact @GlobalTheory.IndLine.LeviK.levi_mem_KAt | exact GlobalTheory.IndLine.LeviK.levi_mem_KAt | (intros; apply GlobalTheory.IndLine.LeviK.levi_mem_KAt <;> assumption)
