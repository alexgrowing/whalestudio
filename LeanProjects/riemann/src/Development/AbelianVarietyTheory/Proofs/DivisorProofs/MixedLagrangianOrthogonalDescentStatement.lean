import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedLagrangianOrthogonalDescent
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariant

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_lagrangian_orthogonal_descent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∀ w : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F),
        (∃ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))), ∃ z : Matrix (Fin n) (Fin d₁) (AE F E),
          (M₁.co.e z).1 = 0 ∧ ∀ φ : Fn F n d,
            schr B.ψ w φ = M.co.rho B.ψ u (M.co.rho B.ψ (incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) φ)) →
        (∀ z : Matrix (Fin n) (Fin d₁) E,
          w.1 ⬝ᵥ (M.co.e (incM F (1 : Matrix (Fin n) (Fin n) E) * incM F z * (incM F H'.ι)ᵀ)).2 =
            (M.co.e (incM F (1 : Matrix (Fin n) (Fin n) E) * incM F z * (incM F H'.ι)ᵀ)).1 ⬝ᵥ w.2) →
        ∃ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))), w = M.co.e u := by
  first | exact @GlobalTheory.MixedLagrOrth.mem_iso_zero_of_orth | exact GlobalTheory.MixedLagrOrth.mem_iso_zero_of_orth | (intros; apply GlobalTheory.MixedLagrOrth.mem_iso_zero_of_orth <;> assumption)
