import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenIntertwinerModelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdaptedModelSkewPlaneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdaptedModelTwoPlanesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerTwoPlanesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueStatement

noncomputable section

namespace GlobalTheory.ThK.EvMaps

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

theorem incM_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) :
    incM F (1 : Matrix (Fin n) (Fin n) E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem vac_mem_SB {B : Base F E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} (hM : M.IsGood B.ψ) (v : Pl F) :
    M.vac v ∈ SB _ :=
  (hM.vac v).1

theorem isEv_comp {B : Base F E} {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
    {M Ma : Model σ X W} {M₁ : Model σ X₁ W₁} {ι : Matrix (Fin n) (Fin n₁) E} {ι' : Matrix (Fin d) (Fin d₁) E}
    {I : Set (Matrix (Fin n) (Fin d) (AE F E))} {e₁ : Fn F n d →ₗ[ℂ] Fn F n d} {e₂ : Fn F n d →ₗ[ℂ] Fn F n₁ d₁}
    (h₁ : IsEv B M Ma 1 1 ∅ e₁) (ei₁ : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
    (ev₁ : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ)
    (hs : Function.Surjective ei₁) (hv₁ : ∀ v, ev₁ v (M.vac v) = Ma.vac v ∧ (SB _).map (ev₁ v) = SB _)
    (hl₁ : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e₁ (pure f φ) = pure (ei₁ f) fun v => ev₁ v (φ v))
    (h₂ : IsEv B Ma M₁ ι ι' I e₂) : IsEv B M M₁ ι ι' I (e₂ ∘ₗ e₁) := by
  have heis₁ : ∀ u, ∀ Φ ∈ schA F (Fin n × Fin d), e₁ (M.co.rho B.ψ u Φ) = Ma.co.rho B.ψ u (e₁ Φ) := by
    intro u Φ hΦ
    have := h₁.Heisenberg₂ u Φ hΦ
    rwa [incM_one, incM_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one] at this
  refine ⟨fun Φ hΦ => h₂.maps _ (h₁.maps Φ hΦ), fun z Φ hΦ => ?_, fun u hu Φ hΦ => ?_, ?_⟩
  · simp only [LinearMap.comp_apply]
    rw [heis₁ _ Φ hΦ, h₂.Heisenberg₂ z _ (h₁.maps Φ hΦ)]
  · simp only [LinearMap.comp_apply]
    rw [heis₁ _ Φ hΦ, h₂.inv u hu _ (h₁.maps Φ hΦ)]
  · obtain ⟨ei₂, ev₂, hne, hv₂, hl₂⟩ := h₂.loc
    refine ⟨ei₂.comp ei₁, fun v => (ev₂ v).comp (ev₁ v), ?_, fun v => ⟨?_, ?_⟩, fun f φ hφ hc => ?_⟩
    · intro h0
      apply hne
      ext1 g
      obtain ⟨g', rfl⟩ := hs g
      exact congrArg (fun T : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁) => T g') h0
    · simp [(hv₁ v).1, (hv₂ v).1]
    · rw [Submodule.map_comp, (hv₁ v).2, (hv₂ v).2]
    · have hφ' : ∀ v, ev₁ v (φ v) ∈ SB _ := fun v => by
        rw [← (hv₁ v).2]; exact Submodule.mem_map_of_mem (hφ v)
      have hc' : ∀ᶠ v in cofinite, ev₁ v (φ v) = Ma.vac v := by
        filter_upwards [hc] with v hv; rw [hv, (hv₁ v).1]
      simp only [LinearMap.comp_apply, ContinuousLinearMap.comp_apply]
      rw [hl₁ f φ hφ hc, hl₂ _ _ hφ' hc']

theorem polData_map (B : Base F E) {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
    (M : Model σ X W) (M₁ : Model σ X₁ W₁) (hM : ∀ v, M.vac v ∈ SB _) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁)
    (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n₁ × Fin d₁))
    (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n₁ × Fin d₁ → Fv F v) → ℂ)
    (hP : (M.Pol B.ψ B.emb).map (ei : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n₁ × Fin d₁)) = M₁.Pol B.ψ B.emb)
    (hv : ∀ v, ev v (M.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _)
    (hl : ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)) :
    (PolData B M).map e = PolData B M₁ := by
  unfold PolData
  rw [Submodule.map_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨Φ, ⟨f, hf, φ, hφ, hc, rfl⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨ei f, ?_, fun v => ev v (φ v), fun v => ?_, ?_, hl f φ hφ hc⟩
    · rw [← hP]; exact Submodule.mem_map_of_mem (f := (ei : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n₁ × Fin d₁))) hf
    · rw [← (hv v).2]; exact Submodule.mem_map_of_mem (hφ v)
    · filter_upwards [hc] with v hv'; rw [hv', (hv v).1]
  · rw [Submodule.span_le]
    rintro _ ⟨g, hg, φ', hφ', hc', rfl⟩
    rw [← hP] at hg
    obtain ⟨f, hf, rfl⟩ := hg
    have hpre : ∀ v, ∃ p, p ∈ SB (Fin n × Fin d → Fv F v) ∧ ev v p = φ' v := fun v => by
      have := hφ' v
      rw [← (hv v).2] at this
      exact this
    classical
    let φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ := fun v => if φ' v = M₁.vac v then M.vac v else (hpre v).choose
    have hφ : ∀ v, φ v ∈ SB _ := fun v => by
      by_cases h : φ' v = M₁.vac v
      · simp only [φ, if_pos h]; exact hM v
      · simp only [φ, if_neg h]; exact (hpre v).choose_spec.1
    have hev : (fun v => ev v (φ v)) = φ' := funext fun v => by
      by_cases h : φ' v = M₁.vac v
      · simp only [φ, if_pos h]; rw [(hv v).1, h]
      · simp only [φ, if_neg h]; exact (hpre v).choose_spec.2
    have hc : ∀ᶠ v in cofinite, φ v = M.vac v := by
      filter_upwards [hc'] with v h; simp only [φ, if_pos h]
    apply Submodule.subset_span
    refine ⟨pure f φ, ⟨f, hf, φ, hφ, hc, rfl⟩, ?_⟩
    rw [hl f φ hφ hc, hev]
    rfl

theorem map_eq_of_smul {A C : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup C] [Module ℂ C] {N : Submodule ℂ A}
    {e e₀ : A →ₗ[ℂ] C} {c : ℂ} (hc : c ≠ 0) (h : ∀ x ∈ N, e x = c • e₀ x) : N.map e = N.map e₀ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨c • x, N.smul_mem c hx, by rw [map_smul, h x hx]⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨c⁻¹ • x, N.smul_mem _ hx, ?_⟩
    rw [h _ (N.smul_mem _ hx), map_smul, smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem evZero_evCone : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.EvZero ∧ GlobalTheory.ThK.EvCone := by
  intro hK
  refine ⟨?_, ?_⟩
  · intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ X₁ W₁ H' i₀ i₁ M₁ hX hH hM₁
    subst X₁
    obtain ⟨Ma, e₂, hMa, h₂, ei₂, ev₂, hP₂, hv₂, hl₂⟩ :=
      GlobalTheory.T.exists_adapted_model_skew_plane hK F E σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M M₁ hP.base hP.herm hP.skew hP.good hH hM₁
    obtain ⟨e₁, h₁, ei₁, ev₁, hs₁, hP₁, hv₁, hl₁⟩ :=
      GlobalTheory.T.exists_eigen_intertwiner_models hK F E σ B n d r s r' s' X W M Ma hP.base hP.herm hP.skew hP.good hMa
    have hE := isEv_comp h₁ ei₁ ev₁ hs₁ hv₁ hl₁ h₂
    have hmap : (PolData B M).map (e₂ ∘ₗ e₁) = PolData B M₁ := by
      rw [Submodule.map_comp, polData_map B M Ma (vac_mem_SB hP.good) e₁ ei₁ ev₁ hP₁ hv₁ hl₁,
        polData_map B Ma M₁ (vac_mem_SB hMa) e₂ ei₂ ev₂ hP₂ hv₂ hl₂]
    refine ⟨⟨_, hE⟩, fun e he => ?_⟩
    obtain ⟨c, hc, hce⟩ :=
      GlobalTheory.T.eigen_intertwiner_skew_plane_unique hK F E σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M M₁ hP.base hP.herm hP.skew hP.good hH hM₁ _ e hE he
    rw [← hmap]
    exact map_eq_of_smul hc hce
  · intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ d₁ X₁ W₁ H H' i₀ i₁ j₀ j₁ M₁ hH hH' hM₁
    refine ⟨?_, ?_⟩
    · obtain ⟨Ma, e₂, hMa, h₂⟩ :=
        GlobalTheory.T.exists_adapted_model_two_planes hK F E σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' M M₁ hP.base hP.herm hP.skew hP.good hH hH' hM₁
      obtain ⟨e₁, h₁, ei₁, ev₁, hs₁, -, hv₁, hl₁⟩ :=
        GlobalTheory.T.exists_eigen_intertwiner_models hK F E σ B n d r s r' s' X W M Ma hP.base hP.herm hP.skew hP.good hMa
      exact ⟨_, isEv_comp h₁ ei₁ ev₁ hs₁ hv₁ hl₁ h₂⟩
    · obtain ⟨Ma, e₂, hMa, h₂⟩ :=
        GlobalTheory.T.eigen_intertwiner_two_planes hK F E σ B n d n₁ d₁ r s r' s' i₀ i₁ j₀ j₁ X W X₁ W₁ H H' M M₁ hP.base hP.herm hP.skew hP.good hH hH' hM₁
      obtain ⟨e₁, h₁, ei₁, ev₁, hs₁, -, hv₁, hl₁⟩ :=
        GlobalTheory.T.exists_eigen_intertwiner_models hK F E σ B n d r s r' s' X W M Ma hP.base hP.herm hP.skew hP.good hMa
      exact ⟨_, isEv_comp h₁ ei₁ ev₁ hs₁ hv₁ hl₁ h₂⟩

end GlobalTheory.ThK.EvMaps

end
