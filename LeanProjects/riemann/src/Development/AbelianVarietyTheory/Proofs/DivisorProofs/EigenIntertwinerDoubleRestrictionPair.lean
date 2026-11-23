import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerDoubleRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerRestrictionCharacterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentQuotientUnitVolumeStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThKSumm

theorem isCartan_restrict {n m : ℕ} (M θ : Matrix (Fin n) (Fin n) ℂ) (ι : Matrix (Fin n) (Fin m) ℂ)
    (L : Matrix (Fin m) (Fin n) ℂ) (hL : L * ι = 1) (θ₁ : Matrix (Fin m) (Fin m) ℂ)
    (h : IsCartan M θ) (hc : θ * ι = ι * θ₁) : IsCartan (ιᵀ * M * ι.map star) θ₁ := by
  obtain ⟨h1, h2, h3⟩ := h
  have hst : ∀ {a b c : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) (B : Matrix (Fin b) (Fin c) ℂ),
      (A * B).map star = A.map star * B.map star := fun A B => by
    simpa using (Matrix.map_mul (f := starRingEnd ℂ) (M := A) (N := B))
  refine ⟨?_, ?_, ?_⟩
  · calc θ₁ * θ₁ = (L * ι) * θ₁ * θ₁ := by rw [hL, one_mul]
      _ = L * (θ * θ) * ι := by
        have e : ι * θ₁ * θ₁ = θ * θ * ι := by
          rw [← hc, Matrix.mul_assoc, ← hc, Matrix.mul_assoc]
        simp only [Matrix.mul_assoc] at e ⊢; rw [e]
      _ = 1 := by rw [h1, Matrix.mul_one, hL]
  · have hc' : (ι * θ₁).map star = (θ * ι).map star := by rw [hc]
    rw [hst, hst] at hc'
    calc θ₁ᵀ * (ιᵀ * M * ι.map star) * θ₁.map star = (ι * θ₁)ᵀ * M * (ι.map star * θ₁.map star) := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = (θ * ι)ᵀ * M * (θ.map star * ι.map star) := by rw [hc', hc]
      _ = ιᵀ * (θᵀ * M * θ.map star) * ι.map star := by
          rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = ιᵀ * M * ι.map star := by rw [h2]
  · intro x hx
    have hy : ι *ᵥ x ≠ 0 := by
      intro h0; apply hx
      have := congrArg (fun v => L *ᵥ v) h0
      simpa [Matrix.mulVec_mulVec, hL] using this
    have key : θ₁ *ᵥ x ⬝ᵥ (ιᵀ * M * ι.map star) *ᵥ star x = θ *ᵥ (ι *ᵥ x) ⬝ᵥ M *ᵥ star (ι *ᵥ x) := by
      have e1 : (ι.map star) *ᵥ star x = star (ι *ᵥ x) := by
        funext i; simp [Matrix.mulVec, dotProduct, star_sum, mul_comm]
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e1, Matrix.dotProduct_mulVec,
        Matrix.vecMul_transpose, Matrix.mulVec_mulVec, ← hc, ← Matrix.mulVec_mulVec]
    rw [key]; exact h3 _ hy

end GlobalTheory.ThKSumm

namespace GlobalTheory.ThKSumm

theorem exists_leftInverse {E : Type} [Field E] {d d₁ : ℕ} (x y : Fin d → E) (ι : Matrix (Fin d) (Fin d₁) E)
    (hrank : d = d₁ + 2)
    (hspan : ⊤ ≤ Submodule.span E (Set.range ![x, y]) ⊔ LinearMap.range (Matrix.mulVecLin ι)) :
    ∃ Lm : Matrix (Fin d₁) (Fin d) E, Lm * ι = 1 := by
  have h1 : Module.finrank E (⊤ : Submodule E (Fin d → E)) ≤
      Module.finrank E (Submodule.span E (Set.range ![x, y])) + Module.finrank E (LinearMap.range (Matrix.mulVecLin ι)) := by
    calc Module.finrank E (⊤ : Submodule E (Fin d → E))
        ≤ Module.finrank E ↥(Submodule.span E (Set.range ![x, y]) ⊔ LinearMap.range (Matrix.mulVecLin ι)) :=
          Submodule.finrank_mono hspan
      _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _
  have h2 : Module.finrank E (Submodule.span E (Set.range ![x, y])) ≤ 2 := by
    have := finrank_range_le_card (R := E) ![x, y]
    exact this
  have h3 := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin ι)
  rw [finrank_top, Module.finrank_fin_fun] at h1
  rw [Module.finrank_fin_fun] at h3
  have hk : Module.finrank E (LinearMap.ker (Matrix.mulVecLin ι)) = 0 := by omega
  have hker : LinearMap.ker (Matrix.mulVecLin ι) = ⊥ := Submodule.finrank_eq_zero.mp hk
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at this

end GlobalTheory.ThKSumm

namespace GlobalTheory.ThKSumm

theorem isIsoPlane_of_adapted {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) {d d₁ : ℕ} (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁)
    (i₀ i₁ r' s' : ℕ) (hcm : IsCMExt F E σ) (hW : W.IsSkew σ B r' s') (hH' : H'.IsAdapted σ B W W₁ i₀ i₁) :
    DescB.IsIsoPlane σ B H' W W₁ := by
  refine DescB.IsIsoPlane.of_adapted hH' hW.cartan fun w => ?_
  have hspan : ⊤ ≤ Submodule.span E (Set.range ![H'.x, H'.y]) ⊔ LinearMap.range (Matrix.mulVecLin H'.ι) := by
    intro z _
    have hz : z ∈ Submodule.span E (W.L : Set (Fin d → E)) := by rw [hW.lat.span_eq_top]; trivial
    refine (Submodule.span_le.mpr ?_) hz
    intro z hz
    obtain ⟨s, t, u, -, -, -, rfl⟩ := hH'.split z hz
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
    · exact Submodule.mem_sup_right ⟨u, rfl⟩
    · exact Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  obtain ⟨Lm, hLm⟩ := exists_leftInverse H'.x H'.y H'.ι hH'.rank hspan
  set φ : E →+* ℂ := (B.emb w : E →+* ℂ) with hφ
  have hconj : ∀ a, φ (σ a) = star (φ a) := hcm.2.2.2 φ
  have hJ : W₁.J.map φ = (H'.ι.map φ)ᵀ * W.J.map φ * (H'.ι.map φ).map star := by
    rw [← hH'.gram, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
    congr 1; ext i j; simp [hconj]
  have hL : Lm.map φ * H'.ι.map φ = 1 := by
    rw [← Matrix.map_mul, hLm, Matrix.map_one _ φ.map_zero φ.map_one]
  rw [hJ, show Complex.I • ((H'.ι.map φ)ᵀ * W.J.map φ * (H'.ι.map φ).map star) =
      (H'.ι.map φ)ᵀ * (Complex.I • W.J.map φ) * (H'.ι.map φ).map star by
    simp [Matrix.mul_smul, Matrix.smul_mul]]
  exact isCartan_restrict _ _ _ _ hL _ (hW.cartan w) (hH'.cartan w).1

end GlobalTheory.ThKSumm

namespace GlobalTheory.ThKSumm

theorem summable_of_isoPlane (hKP : GlobalTheory.ThK.KP) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ)
    (hH' : H'.IsAdapted σ B W W₁ i₀ i₁) (hM₁ : M₁.IsGood B.ψ) (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁) (he₀ : IsEv B M M₁ 1 H'.ι (iso0 n H') e₀)
    (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ W₁) (hH : H.IsAdapted σ B X X₁ j₀ j₁) (hM₂ : M₂.IsGood B.ψ)
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁) (he : IsEv B M M₂ H.ι H'.ι (isoA H H') e)
    (γ : {x : Fin n → E // x ≠ 0 ∧ form σ X.J x x = 0} → UA σ X.J) (hγ : ∀ x, γ x ∈ ratU σ X.J ∧ mat (γ x) *ᵥ incV F x.1 = incV F H.x)
    (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ) (hP : IsPair B M χX χW om r s r' s') (Ψ : Fn F n d) (hΨ : Ψ ∈ schA F (Fin n × Fin d))
    (hiso : DescB.IsIsoPlane σ B H' W W₁) :
    Summable fun x => thetaSum F (e (M.co.rho B.ψ (shiftA H H' 1) (om (γ x, 1) Ψ))) := by
  obtain ⟨C, hC0, hC⟩ := GlobalTheory.T.eigen_intertwiner_double_restriction hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e he
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ := GlobalTheory.T.unipotent_quotient_unit_volume F E σ B hP.base d d₁ W W₁ H' hP.skew.skew hiso
  have hS := (GlobalTheory.T.eigen_intertwiner_restriction_character hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ χX χW om r s r' s' hP μ 𝓕 hμ h𝓕 h1 Ψ hΨ).1
  have hS' := (hS.subtype {x : Fin n → E | x ≠ 0 ∧ form σ X.J x x = 0}).mul_left C⁻¹
  refine hS'.congr fun x => ?_
  simp only [Function.comp_apply]
  rw [hC χX χW om r s r' s' hP μ 𝓕 hμ h𝓕 h1 Ψ hΨ x.1 x.2.1 x.2.2 (γ x) (hγ x).1 (hγ x).2, ← mul_assoc, inv_mul_cancel₀ hC0, one_mul]

theorem summable_isotropic : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ → ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → M₂.IsGood B.ψ →
    ∀ e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁, IsEv B M M₂ H.ι H'.ι (isoA H H') e →
    ∀ γ : {x : Fin n → E // x ≠ 0 ∧ form σ X.J x x = 0} → UA σ X.J, (∀ x, γ x ∈ ratU σ X.J ∧ mat (γ x) *ᵥ incV F x.1 = incV F H.x) →
    ∀ (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Ψ ∈ schA F (Fin n × Fin d), Summable fun x => thetaSum F (e (M.co.rho B.ψ (shiftA H H' 1) (om (γ x, 1) Ψ))) := by
  intro hKP F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e he γ hγ χX χW om r s r' s' hP Ψ hΨ
  exact summable_of_isoPlane hKP F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e he γ hγ
    χX χW om r s r' s' hP Ψ hΨ (isIsoPlane_of_adapted σ B W W₁ H' i₀ i₁ r' s' hP.base.cm hP.skew hH')

end GlobalTheory.ThKSumm
