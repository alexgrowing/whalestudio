import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviTorusElementCm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levi_torus_element_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (r s i₀ i₁ : ℕ), IsCMExt F E σ → W.IsSkew σ B r s → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ t : (AE F E)ˣ, ∃ m : UA σ W.J, IsLevi (W₁ := W₁) H' t 1 m := by
  first | exact @GlobalTheory.ThK.exists_isLevi | exact GlobalTheory.ThK.exists_isLevi | (intros; apply GlobalTheory.ThK.exists_isLevi <;> assumption)
