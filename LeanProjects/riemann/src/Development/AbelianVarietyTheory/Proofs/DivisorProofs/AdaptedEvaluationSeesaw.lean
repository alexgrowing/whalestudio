import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFinitePureTensors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedModelsEigenCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelsPairPlaneAdaptedGoodStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenMapExistsSignatureModelsStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK.IsoComp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem incM_one (k : ℕ) : incM F (1 : Matrix (Fin k) (Fin k) E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem vecMulVec_mulVec {m k l : ℕ} (a : Fin m → AE F E) (P : Matrix (Fin k) (Fin l) (AE F E)) (z : Fin l → AE F E) :
    Matrix.vecMulVec a (P *ᵥ z) = Matrix.vecMulVec a z * Pᵀ := by
  ext i j
  simp [Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

end GlobalTheory.ThK.IsoComp

open GlobalTheory.ThK.IsoComp in

theorem GlobalTheory.ThK.IsoComp.main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → M₂.IsGood B.ψ → B.IsGood σ → M.IsGood B.ψ → (∃ r s r' s' : ℕ, X.IsHerm σ B r s ∧ W.IsSkew σ B r' s') →
    ∀ e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁, IsEv B M M₂ H.ι H'.ι (isoA H H') e →
    ∃ e' : Fn F n d₁ →ₗ[ℂ] Fn F n₁ d₁, IsEv B M₁ M₂ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e' ∧
      ∃ c : ℂ, c ≠ 0 ∧ ∀ Ψ ∈ schA F (Fin n × Fin d), e' (e₀ Ψ) = c • e Ψ := by
  intro hKP F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ n₁ X₁ H j₀ j₁ M₂ hH hM₂ hB hM hXW e he
  obtain ⟨e', he'⟩ := GlobalTheory.T.adapted_models_eigen_compatible hKP F E σ B n d d₁ X W W₁ M₁ H' i₀ i₁ hH' hM₁ n₁ X₁ H j₀ j₁ M₂ hH hM₂ hB hXW
  refine ⟨e', he', ?_⟩

  have hne : ∃ Ψ ∈ schA F (Fin n × Fin d), e' (e₀ Ψ) ≠ 0 := by
    obtain ⟨Ψ₁, hΨ₁, h1⟩ := GlobalTheory.T.eigen_intertwiner_extension F E σ B n d₁ n₁ d₁ X W₁ X₁ W₁ M₁ M₂ H.ι 1 _ e' hM₁ hM₂ he'
    obtain ⟨Ψ, hΨ, rfl⟩ := GlobalTheory.T.eigen_map_exists_signature_models hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hB hXW hM hM₁ hH' e₀ he₀ Ψ₁ hΨ₁
    exact ⟨Ψ, hΨ, h1⟩
  obtain ⟨ei₀, ev₀, h0ne, h0v, h0loc⟩ := he₀.loc
  obtain ⟨ei', ev', h1ne, h1v, h1loc⟩ := he'.loc
  have hSB : ∀ v, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ev₀ v φ ∈ SB (Fin n × Fin d₁ → Fv F v) := fun v φ hφ => by
    rw [← (h0v v).2]
    exact Submodule.mem_map_of_mem hφ
  have hcomp : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) →
      e' (e₀ (pure f φ)) = pure (ei' (ei₀ f)) fun v => ev' v (ev₀ v (φ v)) := fun f φ hφ hφv => by
    rw [h0loc f φ hφ hφv, h1loc (ei₀ f) (fun v => ev₀ v (φ v)) (fun v => hSB v _ (hφ v))]
    filter_upwards [hφv] with v hv
    rw [hv, (h0v v).1]

  have hine : ei'.comp ei₀ ≠ 0 := by
    intro h0
    obtain ⟨Ψ, hΨ, hne⟩ := hne
    apply hne
    obtain ⟨T, m, f, φ, hφ, hT, rfl⟩ := GlobalTheory.SchADecomp.exists_sum_pure F (Fin n × Fin d) Ψ hΨ
    rw [map_sum, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    have hv : ∀ᶠ v in cofinite, φ i v = M.vac v := by
      filter_upwards [hM.std, (Set.Finite.compl_mem_cofinite T.finite_toSet : (↑T : Set (Pl F))ᶜ ∈ cofinite)] with v h1 h2
      rw [h1, hT i v h2]
    rw [hcomp (f i) (φ i) (hφ i) hv]
    have : ei' (ei₀ (f i)) = 0 := by
      simpa using congrArg (fun L : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁) => L (f i)) h0
    funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, this]
  have hev : IsEv B M M₂ H.ι H'.ι (isoA H H') (e'.comp e₀) := by
    refine ⟨fun Φ hΦ => he'.maps _ (he₀.maps Φ hΦ), fun z Φ hΦ => ?_, fun u hu Φ hΦ => ?_,
      ⟨ei'.comp ei₀, fun v => ev' v ∘ₗ ev₀ v, hine, fun v => ⟨?_, ?_⟩, fun f φ hφ hφv => ?_⟩⟩
    · have h1 := he₀.Heisenberg₂ (incM F H.ι * z) Φ hΦ
      rw [incM_one, Matrix.one_mul] at h1
      have h2 := he'.Heisenberg₂ z (e₀ Φ) (he₀.maps Φ hΦ)
      rw [incM_one, Matrix.transpose_one, Matrix.mul_one] at h2
      simp only [LinearMap.comp_apply]
      rw [h1, h2]
    · rcases hu with hu | ⟨z, rfl⟩
      · simp only [LinearMap.comp_apply]
        rw [he₀.inv u hu Φ hΦ]
      · have h1 := he₀.Heisenberg₂ (Matrix.vecMulVec (incV F H.x) z) Φ hΦ
        rw [incM_one, Matrix.one_mul, ← vecMulVec_mulVec] at h1
        simp only [LinearMap.comp_apply]
        rw [h1, he'.inv _ ⟨z, rfl⟩ _ (he₀.maps Φ hΦ)]
    · simp only [LinearMap.comp_apply]
      rw [(h0v v).1, (h1v v).1]
    · rw [Submodule.map_comp, (h0v v).2, (h1v v).2]
    · simp only [LinearMap.comp_apply, ContinuousLinearMap.comp_apply]
      exact hcomp f φ hφ hφv
  obtain ⟨c, hc⟩ := GlobalTheory.T.models_pair_plane_adapted_good hKP F E σ B n d n₁ d₁ X W X₁ W₁ M M₂ H H' i₀ i₁ j₀ j₁ hB hXW hM hM₂ hH hH' e _ he hev
  refine ⟨c, fun hc0 => ?_, fun Ψ hΨ => hc Ψ hΨ⟩
  obtain ⟨Ψ, hΨ, hne⟩ := hne
  exact hne (by simpa [hc0] using hc Ψ hΨ)
