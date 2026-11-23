import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairPlaneDescent
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_pair_plane_descent : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (H : Plane E n n₁) (H' : Plane E d d₁) (j₀ j₁ i₀ i₁ : ℕ) (Mb : Model σ X₁ W) (omb : Rep σ X₁ W) (r₁ s₁ : ℕ)
    (M₁ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B Mb χX χW omb r₁ s₁ r' s' → M₁.IsGood B.ψ →
    ∀ e₁ e₂, IsEv B M Mb H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e₁ → IsEv B Mb M₁ 1 H'.ι (iso0 n₁ H') e₂ →
    ∃ Φ ∈ schA F (Fin n × Fin d), e₂ (e₁ Φ) ≠ 0 := by
  first | exact @GlobalTheory.ThK.EvTwoNeB.comp_ne_zero | exact GlobalTheory.ThK.EvTwoNeB.comp_ne_zero | (intros; apply GlobalTheory.ThK.EvTwoNeB.comp_ne_zero <;> assumption)
