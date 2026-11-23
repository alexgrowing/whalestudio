import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocFieldLP
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantOfIsSkew
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFundamentalDomainMulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.LiftPair
open scoped Matrix TensorProduct

noncomputable section

namespace GlobalTheory.RightTransFD

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem isMulRightInvariant_skewND {σ : E →ₐ[F] E} (hcm : IsCMExt F E σ) {m : ℕ} (J : Matrix (Fin m) (Fin m) E)
    (hJ : ∀ i j, σ (J j i) = -J i j) (hd : J.det ≠ 0) (μ : Measure (UA σ J)) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant := by
  have hσ := GlobalTheory.SiegelSet.sigma_sigma hcm
  obtain ⟨δ, hδ, hσδ⟩ := GlobalTheory.HermUnimod.exists_anti hcm
  have hJ' : IsHermND σ (δ • J.map σ) := by
    refine ⟨fun i j => ?_, ?_⟩
    · simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, hσ, hσδ]
      rw [hJ j i]
      ring
    · rw [Matrix.det_smul, show J.map σ = (σ : E →+* E).mapMatrix J from rfl, ← RingHom.map_det]
      exact mul_ne_zero (pow_ne_zero _ hδ) ((map_ne_zero _).2 hd)
  have heq : GlobalTheory.WeilM.UG (cA σ) (incM F J) = HR (AF F) σ (δ • J.map σ) :=
    GlobalTheory.SiegelSet.ug_eq_hr (F := F) (J := J) hσ hδ
  let e : UA σ J ≃* HA (AF F) σ (δ • J.map σ) := MulEquiv.subgroupCongr heq
  have he : Continuous e := continuous_subtype_val.subtype_mk _
  have he' : Continuous e.symm := continuous_subtype_val.subtype_mk _
  haveI : BorelSpace (UA σ J) := ⟨rfl⟩
  haveI : BorelSpace (HA (AF F) σ (δ • J.map σ)) := ⟨rfl⟩
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : IsTopologicalGroup (HA (AF F) σ (δ • J.map σ)) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF F) σ (δ • J.map σ)))
  haveI : ContinuousMul (UA σ J) := ⟨by
    have h3 : (fun p : UA σ J × UA σ J => p.1 * p.2) = fun p => e.symm (e p.1 * e p.2) :=
      funext fun p => by rw [← map_mul, MulEquiv.symm_apply_apply]
    rw [h3]
    exact he'.comp ((he.comp continuous_fst).mul (he.comp continuous_snd))⟩
  haveI : (μ.map e).IsHaarMeasure := MulEquiv.isHaarMeasure_map μ e he he'
  have hR : (μ.map e).IsMulRightInvariant :=
    GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_adelic σ hσ hδ hσδ hJ' (μ.map e)
  have hem : Measurable e := he.measurable
  have hem' : Measurable e.symm := he'.measurable
  refine ⟨fun g => ?_⟩
  have hmg : Measurable fun y : HA (AF F) σ (δ • J.map σ) => y * e g := (continuous_mul_right (e g)).measurable
  have h1 : (μ.map e).map e.symm = μ := by
    rw [Measure.map_map hem' hem]
    have : (e.symm ∘ e : UA σ J → UA σ J) = id := funext fun x => e.symm_apply_apply x
    rw [this, Measure.map_id]
  have h2 : ((μ.map e).map (fun y => y * e g)).map e.symm = μ.map (· * g) := by
    rw [Measure.map_map hmg hem, Measure.map_map hem' (hmg.comp hem)]
    congr 1
  rw [← h2, hR.map_mul_right_eq_self (e g), h1]

theorem setIntegral_fd_mul_right : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (m : ℕ) (JY : Matrix (Fin m) (Fin m) E), (∀ i j, σ (JY j i) = -JY i j) → JY.det ≠ 0 → ∀ (μ : Measure (UA σ JY)) (𝓕 : Set (UA σ JY)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ JY) 𝓕 μ → ∀ F₁ : UA σ JY → ℂ, (∀ γ ∈ ratU σ JY, ∀ h, F₁ (γ * h) = F₁ h) → ∀ x : UA σ JY, (IntegrableOn F₁ 𝓕 μ → IntegrableOn (fun h => F₁ (h * x)) 𝓕 μ) ∧ ∫ h in 𝓕, F₁ (h * x) ∂μ = ∫ h in 𝓕, F₁ h ∂μ := by
  intro F E _ _ _ _ _ σ hcm m JY hJ hd μ 𝓕 hμ h𝓕 F₁ hF₁ x
  obtain ⟨_, _, _, _⟩ := GlobalTheory.UnipCT.topFacts σ JY
  haveI : BorelSpace (UA σ JY) := ⟨rfl⟩
  haveI : μ.IsMulRightInvariant := isMulRightInvariant_skewND hcm JY hJ hd μ
  haveI : Countable (ratU σ JY) := GlobalTheory.UnipCT.countable_ratU (σ := σ) JY
  exact ⟨fun hi => GlobalTheory.ThetaCplV.integrableOn_mul_right h𝓕 F₁ hF₁ hi x,
    GlobalTheory.ThetaCplV.setIntegral_mul_right h𝓕 F₁ hF₁ x⟩

end GlobalTheory.RightTransFD
