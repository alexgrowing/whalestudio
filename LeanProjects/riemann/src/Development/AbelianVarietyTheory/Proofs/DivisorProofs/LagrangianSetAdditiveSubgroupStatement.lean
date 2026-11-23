import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianSetAdditiveSubgroup
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.plane_transform_restriction : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E)
    (n d d₁ r s r' s' i₀ i₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (M : Model σ X W)
    (M₁ : Model σ X W₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → H'.IsAdapted σ B W W₁ i₀ i₁ →
    (0 ∈ lagSet M M₁ H') ∧ (∀ l ∈ lagSet M M₁ H', ∀ l' ∈ lagSet M M₁ H', l + l' ∈ lagSet M M₁ H') ∧
    (∀ t : ℝ, ∀ l ∈ lagSet M M₁ H', t • l ∈ lagSet M M₁ H') ∧
    (∀ l ∈ lagSet M M₁ H', ∀ l' ∈ lagSet M M₁ H', trP F _ l.1 l'.2 = trP F _ l'.1 l.2) ∧
    ∀ v, (∀ l ∈ lagSet M M₁ H', trP F _ v.1 l.2 = trP F _ l.1 v.2) → v ∈ lagSet M M₁ H' := by
  first | exact @GlobalTheory.ArchSch.lagSet_isLagrangian | exact GlobalTheory.ArchSch.lagSet_isLagrangian | (intros; apply GlobalTheory.ArchSch.lagSet_isLagrangian <;> assumption)
