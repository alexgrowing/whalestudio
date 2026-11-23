import Development.WeilBound.ThetaLifts.LeviDeterminants.EvStmt
import Development.WeilBound.ThetaLifts.LeviDeterminants.EvChange
import Development.WeilBound.ThetaLifts.LeviDeterminants.LagrangianUniqueness.GeoLeaves

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace PositivityTheory.ThKF0

theorem evaluation_at_zero_unique : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ r s r' s' i₀ i₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (M : Model σ X W)
    (M₁ : Model σ X W₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    M₁.IsGood B.ψ → ∀ e e' : Fn F n d →ₗ[ℂ] Fn F n d₁, IsEv B M M₁ 1 H'.ι (iso0 n H') e → IsEv B M M₁ 1 H'.ι (iso0 n H') e' →
      ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ PolData B M, e' Φ = c • e Φ := by
  intro F E _ _ _ _ _ σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M M₁ hB hX hW hM hH hM₁ e e' he he'
  have adm : ∀ e, IsEv B M M₁ 1 H'.ι (iso0 n H') e →
      (LinearMap.proj 0 : Fn F n d₁ →ₗ[ℂ] ℂ) ∘ₗ e ∈ (adeleClass F).adm (Fin n × Fin d) := fun e he =>
    evaluation_intertwining_of_models F E σ B n d n d₁ X W X W₁ M M₁ 1 H'.ι (iso0 n H') e hM hM₁ he _ (Geo.proj_adm F _ 0)
  obtain ⟨Φ₁, hΦ₁, hne'⟩ := evaluation_intertwining_support F E σ B n d n d₁ X W X W₁ M M₁ 1 H'.ι (iso0 n H') e' hM hM₁ he'
  obtain ⟨c, key⟩ := Geo.map_line lagLine hB.std (Geo.hasLagrangian_skew_adapted hB M M₁ hM hM₁ hH) e' e he'.Heisenberg₂ he.Heisenberg₂ he'.inv he.inv (adm e' he')
    (adm e he) (evaluation_intertwining_support F E σ B n d n d₁ X W X W₁ M M₁ 1 H'.ι (iso0 n H') e hM hM₁ he)
  refine ⟨c, fun h0 => hne' (by rw [key _ hΦ₁, h0, zero_smul]), fun Φ hΦ => key Φ (Submodule.span_le.2 ?_ hΦ)⟩
  rintro _ ⟨f, -, φ, h1, h2, rfl⟩
  exact Submodule.subset_span ⟨f, _, Change.finPr_mem φ h1 (by filter_upwards [h2, hM.std] with v a b using a.trans b), rfl⟩

end PositivityTheory.ThKF0
