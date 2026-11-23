import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAdaptedPlaneRestriction
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
theorem _root_.GlobalTheory.T.pair_adapted_plane_restriction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ →
      ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ →
      ∃ (Y₀ : Submodule F (Fin n × Fin d → F)) (S : Fn F n d → Fn F n d),
        (∀ φ ∈ schA F (Fin n × Fin d), S φ ∈ schA F (Fin n × Fin d)) ∧
        (∀ Φ ∈ schA F (Fin n × Fin d), ∃ φ ∈ schA F (Fin n × Fin d), S φ = Φ) ∧
        (∀ l ∈ (adeleClass F).adm (Fin n × Fin d), ∃ l' ∈ (adeleClass F).adm (Fin n × Fin d),
          ∀ φ ∈ schA F (Fin n × Fin d), l' φ = l (S φ)) ∧
        (∀ (t : AF F), ∀ y ∈ Y₀, ∃ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))),
          ∀ φ ∈ schA F (Fin n × Fin d), S (schr B.ψ (0, t • fun i => algebraMap F (AF F) (y i)) φ) = M.co.rho B.ψ u (S φ)) ∧
        (∀ φ ∈ schA F (Fin n × Fin d), e₀ (S φ) = 0 →
          ∀ x : Fin n × Fin d → AF F, (∀ y ∈ Y₀, x ⬝ᵥ (fun i => algebraMap F (AF F) (y i)) = 0) → φ x = 0) := by
  first | exact @GlobalTheory.StraightEv0.main | exact GlobalTheory.StraightEv0.main | (intros; apply GlobalTheory.StraightEv0.main <;> assumption)
