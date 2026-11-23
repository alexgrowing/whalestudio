import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.HeightProofs.CocompactTensor
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

namespace GlobalTheory.RealWeilF

theorem exists_compact_cover (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (nS nT : ℕ) : ∃ K : Set (WOF F E nS nT), IsCompact K ∧ ∀ x : WOF F E nS nT, ∃ γ ∈ ratLF F E nS nT, γ + x ∈ K := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨K, hK, hx⟩ := GlobalTheory.AdelicMatrixLattice.cocompact_tensor (F := F) (E := E) (AF F)
    (GlobalTheory.AdeleCocompact.exists_compact_adele F)
  choose c hc using hx
  refine ⟨Set.univ.pi fun _ : Fin nT => Set.univ.pi fun _ : Fin nS => K,
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK, fun x => ?_⟩
  exact ⟨_, ⟨Matrix.of fun i j => c (x i j), rfl⟩, fun i _ j _ => hc (x i j)⟩

theorem continuous_rhoBF (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (nS nT : ℕ)
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (ψ : AddChar (AF F) ℂ)
    (hψ : IsCharAF F ψ) : ∀ f : BBF σ JS JT ξ₀ ψ, Continuous fun w => rhoBF σ JS JT ξ₀ ψ hψ w f := by
  intro f
  obtain ⟨K, hK, hc⟩ := exists_compact_cover F E nS nT
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  let G : C(WOF F E nS nT × K, ℂ) := ⟨fun p => heisOF σ JS JT ξ₀ ψ p.1 f.1 p.2,
    (hψ.1.comp (continuous_symplOHF σ JS JT ξ₀ (continuous_subtype_val.comp continuous_snd) continuous_fst)).mul
      (f.1.continuous.comp ((continuous_subtype_val.comp continuous_snd).add continuous_fst))⟩
  refine continuous_iff_continuousAt.2 fun w₀ => ?_
  have h1 := tendsto_iff_norm_sub_tendsto_zero.1 (G.curry.continuous.tendsto w₀)
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun _ => norm_nonneg _) (fun w => ?_) h1)
  refine norm_QB_le _ (norm_nonneg _) fun x => ?_
  obtain ⟨γ, hγ, h⟩ := hc x
  rw [← BBF_norm_periodic hψ _ γ hγ]
  exact (G.curry w - G.curry w₀).norm_coe_le_norm ⟨γ + x, h⟩

end GlobalTheory.RealWeilF

example : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (nS nT : ℕ)
    (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ), ∀ f : BBF σ JS JT ξ₀ ψ, Continuous fun w => rhoBF σ JS JT ξ₀ ψ hψ w f := GlobalTheory.RealWeilF.continuous_rhoBF
