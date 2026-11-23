import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeInvariantPlaneTransform
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacGlueIndicator
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneCo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_invariant_plane_transform : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
    (H : Plane E n n₁) (H' : Plane E d d₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' →
    H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ (v : Pl F), ∀ γ ∈ latAtV X W v,
    (∃ a ∈ latAtV X W v, planeT σ X W H H' a = ((0, (planeT σ X W H H' γ).1.2), 0)) ∧
    (∃ b ∈ latAtV X W v, planeT σ X W H H' b = (((planeT σ X W H H' γ).1.1, 0), 0)) ∧
    (planeT σ X W H H' γ).2 ∈ latAtV X₁ W₁ v := by
  first | exact @GlobalTheory.ThK.PlaneCo.LatDec.latAtV_dec | exact GlobalTheory.ThK.PlaneCo.LatDec.latAtV_dec | (intros; apply GlobalTheory.ThK.PlaneCo.LatDec.latAtV_dec <;> assumption)
