import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanesDarbouxReordering
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExtendByZeroAdd
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.AdaptEv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adapted_planes_darboux_reordering : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (H : Plane E n n₁) (H' : Plane E d d₁) (M₁ : Model σ X₁ W₁)
    (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d))
    (eq : Fin n × Fin d ≃ Fin (2 * (n + d₁)) ⊕ (Fin n₁ × Fin d₁)), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ →
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    (∀ z, co.e (incM F H.ι * z * (incM F H'.ι)ᵀ) = (ext0 eq (M₁.co.e z).1, ext0 eq (M₁.co.e z).2)) →
    (∀ u ∈ isoA H H', (co.e u).1 = 0 ∧ ∀ j, (co.e u).2 (eq.symm (Sum.inr j)) = 0) →
    (∀ u ∈ isoAd H H', (co.e u).2 = 0 ∧ ∀ j, (co.e u).1 (eq.symm (Sum.inr j)) = 0) →
    ∃ A : ∀ v : Pl F, (Fin (2 * (n + d₁)) → Fv F v) → ℂ,
      (∀ v, A v ∈ SB _ ∧ A v 0 = 1 ∧
        Model.IsVac (Model.mk (σ := σ) (X := X) (W := W) co (fun _ => 0) 0 ∅) B.ψ v (prodVac eq (A v) (M₁.vac v))) ∧
      ∀ᶠ v in cofinite, A v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  first | exact @GlobalTheory.ThK.AdaptEv.exists_vac_adapted_isoA | exact GlobalTheory.ThK.AdaptEv.exists_vac_adapted_isoA | (intros; apply GlobalTheory.ThK.AdaptEv.exists_vac_adapted_isoA <;> assumption)
