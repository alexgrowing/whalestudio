import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftAdaptedGrowth
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsLeSup
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_adapted_growth : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a a') (Rf : FinMaps F a a'),
    IsMatched B G X om om' R Rf →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ →
      ∀ f ∈ thetaSpanV B G X om R Rf, ∀ g ∈ thetaSpanV' B G X om' R Rf, ∀ c d : UA σ G.W.J → ℂ,
        IsCT H' f c → IsCT H' g d → IsCT H' (f + g) (c + d) := by
  first | exact @GlobalTheory.ThK.DescB.isCT_add_thetaSpan | exact GlobalTheory.ThK.DescB.isCT_add_thetaSpan | (intros; apply GlobalTheory.ThK.DescB.isCT_add_thetaSpan <;> assumption)
