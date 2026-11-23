import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneDarbouxCoordinatesExist
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneZeroInsertionLinearApply
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneEv

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_plane_darboux_coordinates_exist : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ r s r' s' i₀ i₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (M₁ : Model σ X W₁)
    (hd : d = d₁ + 2), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ →
    ∃ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d), ((∀ z : Matrix (Fin n) (Fin d₁) (AE F E), co.e (z * (incM F H'.ι)ᵀ) = (ins0 hd (M₁.co.e z).1, ins0 hd (M₁.co.e z).2)) ∧
      (∀ a : Fin n → AE F E, (co.e (Matrix.vecMulVec a (incV F H'.x))).1 = 0 ∧
        ∀ p, (co.e (Matrix.vecMulVec a (incV F H'.x))).2 ((idx hd).symm (Sum.inl p)) = 0) ∧
      (∀ b : Fin n → AE F E, (co.e (Matrix.vecMulVec b (incV F H'.y))).2 = 0 ∧
        ∀ p, (co.e (Matrix.vecMulVec b (incV F H'.y))).1 ((idx hd).symm (Sum.inl p)) = 0) ∧
      ∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) := by
  first | exact @GlobalTheory.ThK.PlaneEv.Coords.exists_coords | exact GlobalTheory.ThK.PlaneEv.Coords.exists_coords | (intros; apply GlobalTheory.ThK.PlaneEv.Coords.exists_coords <;> assumption)
