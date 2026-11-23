import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaDecompNonsplitPlace
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_decomp_nonsplit_place : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r s r₁ s₁ : ℕ), B.IsGood σ →
    W.IsSkew σ B r s → W₁.IsSkew σ B r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) →
    ∀ h ∈ UAt σ W (evFin F v), ∃ (n m k : UA σ W.J) (t : (AE F E)ˣ) (h₁ : UA σ W₁.J), n ∈ unip σ W H' ∧
      n ∈ UAt σ W (evFin F v) ∧ m ∈ UAt σ W (evFin F v) ∧ h₁ ∈ UAt σ W₁ (evFin F v) ∧ IsLevi H' t h₁ m ∧
      k ∈ KAt σ W v ∧ h = n * m * k := by
  first | exact @GlobalTheory.IwLineInert.iwasawa_line | exact GlobalTheory.IwLineInert.iwasawa_line | (intros; apply GlobalTheory.IwLineInert.iwasawa_line <;> assumption)
