import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPlanePairConverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicStoneVonNeumannLagrangianUniquenessStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigATripleSeesawStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section
namespace GlobalTheory.ThKUniqA

theorem main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ e' : Fn F (b + 2) (b + 2 + a') →ₗ[ℂ] Fn F b (b + a'),
    (∀ z, ∀ Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), e' (G.M.co.rho B.ψ (incM F H.ι * z * (incM F H'.ι)ᵀ) Φ) = G₁.M.co.rho B.ψ z (e' Φ)) →
    (∀ u ∈ isoA (F := F) H H', ∀ Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), e' (G.M.co.rho B.ψ u Φ) = e' Φ) →
    (∀ y : Fin b × Fin (b + a') → AF F, (LinearMap.proj y : Fn F b (b + a') →ₗ[ℂ] ℂ) ∘ₗ e' ∈ (adeleClass F).adm (Fin (b + 2) × Fin (b + 2 + a'))) →
    ∃ c : ℂ, ∀ Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), e' Φ = c • e Φ := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ e' hheis hinv hpt
  have hP := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).1
  have hP₁ := (GlobalTheory.ThK.Check.isPair_of_isTriple hT₁).1
  have hstd : IsStd B.ψ := hP.base.std
  let δ : Fn F b (b + a') →ₗ[ℂ] ℂ := LinearMap.proj 0
  have hδ : δ ∈ (adeleClass F).adm (Fin b × Fin (b + a')) := GlobalTheory.EvZeroUniq.proj_zero_mem_adm F _
  have hρ : ∀ u, ∀ Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), G.M.co.rho B.ψ u Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')) :=
    fun u Φ hΦ => GlobalTheory.EvZeroUniq.schr_mem_schA _ hstd _ hΦ
  have hδe : ∀ (f : Fn F b (b + a')) x, f x = δ (G₁.M.co.rho B.ψ (G₁.M.co.e.symm (x, 0)) f) := fun f x =>
    GlobalTheory.EvZeroUniq.apply_eq_rho _ _ f x
  have hfix : ∀ z, (G₁.M.co.e z).1 = 0 → ∀ f : Fn F b (b + a'), δ (G₁.M.co.rho B.ψ z f) = δ f :=
    fun z hz f => GlobalTheory.EvZeroUniq.rho_apply_zero _ _ f z hz
  obtain ⟨Φ₀, hΦ₀, hne⟩ := GlobalTheory.T.eigen_intertwiner_extension F E σ B _ _ _ _ G.V G.W G₁.V G₁.W G.M G₁.M H.ι H'.ι _ e hP.good hP₁.good he
  obtain ⟨x₀, hx₀⟩ : ∃ x, e Φ₀ x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  obtain ⟨L, hLiso, hLrank, hL⟩ := GlobalTheory.T.config_a_triple_seesaw hKP F E σ B b a' G G₁ H H' hC X om om' om₁ om₁' hT hT₁
  have hinvL : ∀ l : Fn F (b + 2) (b + 2 + a') →ₗ[ℂ] ℂ, (∀ u ∈ isoA (F := F) H H',
      ∀ Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')), l (G.M.co.rho B.ψ u Φ) = l Φ) →
      (∀ z : Matrix (Fin b) (Fin (b + a')) (AE F E), (G₁.M.co.e z).1 = 0 → ∀ Φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')),
        l (G.M.co.rho B.ψ (incM F H.ι * z * (incM F H'.ι)ᵀ) Φ) = l Φ) →
      ∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')),
        l (schr B.ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l φ := by
    intro l h1 h2 t w hw φ hφ
    obtain ⟨u₁, hu₁, u₂, hu₂, z, hz, heq⟩ := hL t w hw
    rw [heq φ, h1 u₁ (Or.inl hu₁) _ (hρ _ _ (hρ _ φ hφ)), h1 u₂ (Or.inr hu₂) _ (hρ _ φ hφ), h2 z hz φ hφ]
  obtain ⟨c, hc⟩ := GlobalTheory.T.adelicStoneVonNeumann_lagrangian_uniqueness F B.ψ hstd (Fin (b + 2) × Fin (b + 2 + a')) L hLiso hLrank (δ ∘ₗ e') (hpt 0) (δ ∘ₗ e)
    (GlobalTheory.T.eigen_intertwiner_good_models F E σ B _ _ _ _ G.V G.W G₁.V G₁.W G.M G₁.M H.ι H'.ι _ e hP.good hP₁.good he δ hδ)
    (hinvL _ (fun u hu Φ hΦ => by simp only [LinearMap.comp_apply]; rw [hinv u hu Φ hΦ])
      (fun z hz Φ hΦ => by simp only [LinearMap.comp_apply]; rw [hheis z Φ hΦ, hfix z hz]))
    (hinvL _ (fun u hu Φ hΦ => by simp only [LinearMap.comp_apply]; rw [he.inv u hu Φ hΦ])
      (fun z hz Φ hΦ => by simp only [LinearMap.comp_apply]; rw [he.Heisenberg₂ z Φ hΦ, hfix z hz]))
    ⟨_, hρ (incM F H.ι * G₁.M.co.e.symm (x₀, 0) * (incM F H'.ι)ᵀ) Φ₀ hΦ₀, by
      simp only [LinearMap.comp_apply]
      rw [he.Heisenberg₂ _ Φ₀ hΦ₀, ← hδe]
      exact hx₀⟩
  refine ⟨c, fun Φ hΦ => funext fun x => ?_⟩
  have h1 := hc _ (hρ (incM F H.ι * G₁.M.co.e.symm (x, 0) * (incM F H'.ι)ᵀ) Φ hΦ)
  simp only [LinearMap.comp_apply] at h1
  rw [hheis _ Φ hΦ, he.Heisenberg₂ _ Φ hΦ, ← hδe, ← hδe] at h1
  simpa using h1

end GlobalTheory.ThKUniqA
