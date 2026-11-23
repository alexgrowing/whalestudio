import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacGlueIndicator
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneCo

namespace GlobalTheory.ThK.PlaneCo

theorem card_coords : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {n d n₁ d₁ i₀ i₁ j₀ j₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (H : Plane E n n₁) (H' : Plane E d d₁), B.IsGood σ →
    H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    Fintype.card (Fin n × Fin d) = Fintype.card (Kc F E d₁ n₁ ⊕ Fin n₁ × Fin d₁) := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ i₀ i₁ j₀ j₁ X W X₁ W₁ H H' hB hH hH'
  obtain ⟨_, _, h2, _⟩ := hB.cm
  obtain rfl := hH.rank
  obtain rfl := hH'.rank
  simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, Kc, Ic, h2]
  ring

end GlobalTheory.ThK.PlaneCo
