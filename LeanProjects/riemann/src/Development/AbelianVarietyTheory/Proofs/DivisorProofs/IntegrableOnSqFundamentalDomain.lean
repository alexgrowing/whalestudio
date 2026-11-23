import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat

noncomputable section

namespace GlobalTheory.ThK.SquareIntegrability

open scoped TensorProduct
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem unitary_of_map_inclR (σ : E →ₐ[F] E) (n : ℕ) (J' : Matrix (Fin n) (Fin n) E) (m : GL (Fin n) E)
    (g : GL (Fin n) (AF F ⊗[F] E)) (hg : g = Matrix.GeneralLinearGroup.map (inclR (F := F) (E := E) (AF F)) m)
    (h : Formalism.UG.cT (sigR (AF F) σ) (g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * JR (AF F) J' *
      (g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) = JR (AF F) J') :
    Formalism.UG.cT (σ : E →+* E) (m : Matrix (Fin n) (Fin n) E) * J' * m = J' := by
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
    Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F)
  subst hg
  apply Matrix.map_injective hinj
  have hs : ∀ x : E, sigR (AF F) σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := fun x => rfl
  dsimp only
  rw [Matrix.map_mul, Matrix.map_mul]
  convert h using 3
  all_goals first
    | rfl
    | exact Matrix.ext fun i j => (hs ((m : Matrix (Fin n) (Fin n) E) j i)).symm

theorem isSqInt_transport : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (c : E) (hc : c ≠ 0)
    (φ : GAd σ (c • J.map σ) → ℂ), IsSqInt σ (c • J.map σ) φ →
    ∀ (μ : Measure (UA σ J)) (𝓕 : Set (UA σ J)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ J) 𝓕 μ →
      IntegrableOn (fun h => ‖φ (toGAd hσ J hc h)‖ ^ 2) 𝓕 μ := by
  intro F E _ _ _ _ _ σ hσ n J c hc φ hφ μ 𝓕 hμ h𝓕
  let e := toGAd hσ J hc
  have he : Continuous e := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  have hes : Continuous e.symm := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  haveI : ContinuousMul (UA σ J) := ⟨by
    have h : (fun p : UA σ J × UA σ J => p.1 * p.2) =
        e.symm ∘ (fun q : GAd σ (c • J.map σ) × GAd σ (c • J.map σ) => q.1 * q.2) ∘ Prod.map e e := by
      funext p
      simp
    rw [h]
    exact hes.comp (continuous_mul.comp (he.prodMap he))⟩
  let t : UA σ J ≃ₜ GAd σ (c • J.map σ) := ⟨e.toEquiv, he, hes⟩
  let me := t.toMeasurableEquiv
  have hp : MeasurePreserving me μ (μ.map me) := ⟨me.measurable, rfl⟩
  have hH : (μ.map me).IsHaarMeasure := MulEquiv.isHaarMeasure_map μ e he hes
  have hps : MeasurePreserving me.symm (μ.map me) μ := hp.symm
  have hmemU : ∀ γ : ratPts σ (c • J.map σ), e.symm γ.1 ∈ ratU σ J := fun γ => by
    obtain ⟨u, -, hu2⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 γ.2)
    exact Subgroup.mem_subgroupOf.2 ⟨u, hu2⟩
  have hmemP : ∀ δ : ratU σ J, e δ.1 ∈ ratPts σ (c • J.map σ) := fun δ => by
    obtain ⟨m, hm⟩ := Subgroup.mem_subgroupOf.1 δ.2
    have h2 := (e δ.1).2
    refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨m, ?_, hm⟩)
    exact unitary_of_map_inclR σ n _ m _ (by rw [hm]; rfl) h2
  let f : ratU σ J → ratPts σ (c • J.map σ) := fun δ => ⟨e δ.1, hmemP δ⟩
  have hf : Function.Bijective f :=
    ⟨fun a b hab => Subtype.ext (e.injective (congrArg Subtype.val hab)),
      fun γ => ⟨⟨e.symm γ.1, hmemU γ⟩, Subtype.ext (e.apply_symm_apply γ.1)⟩⟩
  have hfd := h𝓕.preimage_of_equiv hps.quasiMeasurePreserving hf fun δ x => by
    show e.symm (e δ.1 * x) = δ.1 * e.symm x
    rw [map_mul, e.symm_apply_apply]
  have h1 := hφ (μ.map me) (me.symm ⁻¹' 𝓕) hH hfd
  have h3 := (hp.integrableOn_comp_preimage me.measurableEmbedding).2 h1
  have hset : me ⁻¹' (me.symm ⁻¹' 𝓕) = 𝓕 := by
    ext x
    simp
  rw [hset] at h3
  exact h3

end GlobalTheory.ThK.SquareIntegrability
