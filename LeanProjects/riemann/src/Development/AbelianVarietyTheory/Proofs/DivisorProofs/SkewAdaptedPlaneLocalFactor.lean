import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPlanePairDualStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPlanePairEigenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPlanePairConstantStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.MixWP

theorem evalZero_levi_unitary : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ) (M₁ : Model σ X W₁) (om₁ : Rep σ X W₁) (r₁ s₁ : ℕ),
      H'.IsAdapted σ B W W₁ i₀ i₁ → IsPair B M₁ χX χW om₁ r s r₁ s₁ → ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      ∀ h₁ m, IsLevi H' 1 h₁ m → ∀ Φ ∈ schA F (Fin n × Fin d), e (om (1, m) Φ) = om₁ (1, h₁) (e Φ) := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA hP₁ e he
  refine GlobalTheory.T.skew_adapted_plane_pair_constant hPr F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA hP₁ e he ?_
  intro h₁ m hm
  obtain ⟨hmaps, hheis, hinv⟩ := GlobalTheory.T.skew_adapted_plane_pair_dual F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA hP₁ e he h₁ m hm
  have hspl := IsUWeilPair.isUSplitting hP.weil
  have hspl₁ := IsUWeilPair.isUSplitting hP₁.weil
  have hadm : ∀ l ∈ (adeleClass F).adm (Fin n × Fin d₁),
      l ∘ₗ (om₁ (1, h₁⁻¹) ∘ₗ e ∘ₗ om (1, m)) ∈ (adeleClass F).adm (Fin n × Fin d) := by
    intro l hl
    have h1 := hspl₁.adm (1, h₁⁻¹) l hl
    have h2 := GlobalTheory.T.eigen_intertwiner_good_models F E σ B n d n d₁ X W X W₁ M M₁ 1 H'.ι (iso0 n H') e hP.good hP₁.good he _ h1
    have h3 := hspl.adm (1, m) _ h2
    simpa [LinearMap.comp_assoc] using h3
  obtain ⟨c, hc⟩ := GlobalTheory.T.skew_adapted_plane_pair_eigen hPr F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ M₁ om₁ r₁ s₁ hA hP₁ e he _ hmaps hheis hinv hadm
  refine ⟨c, fun Φ hΦ => ?_⟩
  have key := hc Φ hΦ
  have hinv1 : ∀ Ψ, om₁ (1, h₁) (om₁ (1, h₁⁻¹) Ψ) = Ψ := by
    intro Ψ
    rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, mul_inv_cancel, Prod.mk_one_one, map_one,
      Module.End.one_apply]
  calc e (om (1, m) Φ) = om₁ (1, h₁) (om₁ (1, h₁⁻¹) (e (om (1, m) Φ))) := (hinv1 _).symm
    _ = om₁ (1, h₁) ((om₁ (1, h₁⁻¹) ∘ₗ e ∘ₗ om (1, m)) Φ) := rfl
    _ = c • om₁ (1, h₁) (e Φ) := by rw [key, map_smul]

end GlobalTheory.MixWP

end
