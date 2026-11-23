import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonsplitUnipotentFactor
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonsplit_unipotent_factor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r s r₁ s₁ : ℕ),
    B.IsGood σ → W.IsSkew σ B r s → W₁.IsSkew σ B r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (v : Pl F), IsEmpty (E →ₐ[F] Fv F v) → ∀ g ∈ UAt σ W (evFin F v),
      ∃ u ∈ unip σ W H', u ∈ UAt σ W (evFin F v) ∧ ∃ (t : (AE F E)ˣ) (h₁ : UA σ W₁.J) (m : UA σ W.J),
        IsLevi H' t h₁ m ∧ m ∈ UAt σ W (evFin F v) ∧ h₁ ∈ UAt σ W₁ (evFin F v) ∧
        ∃ k ∈ KAt σ W v, g = u * m * k := by
  first | exact @GlobalTheory.IwasawaLineInert.iwasawa_line_inert | exact GlobalTheory.IwasawaLineInert.iwasawa_line_inert | (intros; apply GlobalTheory.IwasawaLineInert.iwasawa_line_inert <;> assumption)
