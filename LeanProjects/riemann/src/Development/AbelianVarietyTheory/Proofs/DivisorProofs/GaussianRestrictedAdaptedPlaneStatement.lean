import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianRestrictedAdaptedPlane
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinatesInsertZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneEv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gaussian_restricted_adapted_plane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ r s r' s' i₀ i₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (M₁ : Model σ X W₁),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → H'.IsAdapted σ B W W₁ i₀ i₁ → GlobalTheory.RealLift.DerEx →
    GlobalTheory.RealLift.ActsLaws → ∃ g : SInf F (Fin n × Fin d₁), ∀ g₀, M₁.IsGauss B.ψ B.emb g₀ → ∃ z : ℂ, g₀ = z • g := by
  first | exact @GlobalTheory.ThK.PlaneEv.vac_line_of_model | exact GlobalTheory.ThK.PlaneEv.vac_line_of_model | (intros; apply GlobalTheory.ThK.PlaneEv.vac_line_of_model <;> assumption)
