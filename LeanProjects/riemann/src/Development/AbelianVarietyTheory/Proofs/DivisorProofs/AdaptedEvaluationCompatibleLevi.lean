import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedModelsEigenExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLinearHeightFormStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedModelsEigenLiftStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measUA

namespace GlobalTheory.ThKIsoSwap

theorem schr_comm {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (a b : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    schr ψ a (schr ψ b φ) = ψ (a.1 ⬝ᵥ b.2 - b.1 ⬝ᵥ a.2) • schr ψ b (schr ψ a φ) := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul]
  have hx : x + a.1 + b.1 = x + b.1 + a.1 := by abel
  rw [hx]
  simp only [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  simp only [add_dotProduct]
  ring

theorem rho_comm {R : Type} [CommRing R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W] {B : W → W → R}
    {κ : Type} [Fintype κ] (d : Darboux B κ) (ψ : AddChar R ℂ) (a b : W) (φ : (κ → R) → ℂ) :
    d.rho ψ a (d.rho ψ b φ) = ψ (B a b) • d.rho ψ b (d.rho ψ a φ) := by
  rw [d.form]
  exact schr_comm ψ (d.e a) (d.e b) φ

theorem thetaSum_smul {F : Type} [Field F] [NumberField F] {κ : Type} (c : ℂ) (Φ : (κ → AF F) → ℂ) :
    thetaSum F (c • Φ) = c * thetaSum F Φ := by
  simp only [thetaSum, Pi.smul_apply, smul_eq_mul]
  exact tsum_mul_left

theorem phase : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → M₂.IsGood B.ψ → ∀ e' : Fn F n d₁ →ₗ[ℂ] Fn F n₁ d₁, IsEv B M₁ M₂ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e' → ∀ (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Ψ ∈ schA F (Fin n × Fin d), ∀ w : Fin d₁ → E,
      ∃ ℓ : unip σ W H' → AF F, Continuous ℓ ∧ ∀ u : unip σ W H',
        thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) (om (1, u.1) Ψ))))) =
          B.ψ (ℓ u) * thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) Ψ)))) := by
  intro hK F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e' he' χX χW om r s r' s' hP Ψ hΨ w
  obtain ⟨L, hLc, hL⟩ := GlobalTheory.T.continuous_linear_height_form F E σ B n d d₁ X W W₁ H' i₀ i₁ hH' H.x H.y w
  refine ⟨fun u => L (mat u.1⁻¹), hLc.comp ?_, fun u => ?_⟩
  · exact Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_subtype_val)
  · obtain ⟨y, b, hy, hK1⟩ := GlobalTheory.T.adapted_models_eigen_extension hK F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ n₁ X₁ H j₀ j₁ hH χX χW om r s r' s' hP u.1 u.2
    have hstd := hP.base.std
    set φ := e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) Ψ) with hφ
    have hφs : φ ∈ schA F (Fin n × Fin d₁) := he₀.maps _ (GlobalTheory.HeisSchA.rho_mem_schA M B.ψ hstd _ Ψ hΨ)
    have hφ' : M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) φ ∈ schA F (Fin n × Fin d₁) :=
      GlobalTheory.HeisSchA.rho_mem_schA M₁ B.ψ hstd _ φ hφs
    rw [hK1 Ψ hΨ, rho_comm, map_smul, he'.inv _ ⟨y, rfl⟩ _ hφ', thetaSum_smul, hL y b _ hy]

local instance borelUA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) : BorelSpace (UA σ J) := ⟨rfl⟩

theorem integral_tsum_of_bound {ι G : Type*} [Countable ι] [MeasurableSpace G] (μ : Measure G) (s : Set G) (hs : μ s ≠ ⊤)
    (f : ι → G → ℂ) (hm : ∀ i, AEStronglyMeasurable (f i) (μ.restrict s)) (C : ℝ)
    (hb : ∀ u, Summable (fun i => ‖f i u‖) ∧ ∑' i, ‖f i u‖ ≤ C) :
    ∫ u in s, (∑' i, f i u) ∂μ = ∑' i, ∫ u in s, f i u ∂μ := by
  have hlin : ∑' i, ∫⁻ u in s, ‖f i u‖ₑ ∂μ ≠ ⊤ := by
    rw [← lintegral_tsum (fun i => (hm i).enorm)]
    refine ne_top_of_le_ne_top (b := ∫⁻ _ in s, ENNReal.ofReal C ∂μ) ?_ (lintegral_mono fun u => ?_)
    · rw [lintegral_const]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by simpa using hs)
    · simp_rw [← ofReal_norm_eq_enorm]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hb u).1]
      exact ENNReal.ofReal_le_ofReal (hb u).2
  exact integral_tsum hm hlin

theorem swap : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ),
    H'.IsAdapted σ B W W₁ i₀ i₁ → M₁.IsGood B.ψ → ∀ (e₀ : Fn F n d →ₗ[ℂ] Fn F n d₁), IsEv B M M₁ 1 H'.ι (iso0 n H') e₀ →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ W₁), H.IsAdapted σ B X X₁ j₀ j₁ → M₂.IsGood B.ψ → ∀ e' : Fn F n d₁ →ₗ[ℂ] Fn F n₁ d₁, IsEv B M₁ M₂ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e' → ∀ (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (μ : Measure (unip σ W H')) (𝓕 : Set (unip σ W H')), μ.IsHaarMeasure →
      IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ Ψ ∈ schA F (Fin n × Fin d),
      ∫ u in 𝓕, ∑' w : Fin d₁ → E, thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) (om (1, u.1) Ψ))))) ∂μ = ∑' w : Fin d₁ → E, ∫ u in 𝓕, thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) (om (1, u.1) Ψ))))) ∂μ := by
  intro hK F E _ _ _ _ _ σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e' he' χX χW om r s r' s' hP μ 𝓕 _ _ h1 Ψ hΨ
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  have hψ := hP.base.std
  choose ℓ hℓc hℓ using phase hK F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e' he' χX χW om r s r' s' hP Ψ hΨ
  have hS := (summable_norm_iff (E := ℂ)).mpr
    (GlobalTheory.T.adapted_models_eigen_lift hK F E σ B n d d₁ X W W₁ M M₁ H' i₀ i₁ hH' hM₁ e₀ he₀ n₁ X₁ H j₀ j₁ M₂ hH hM₂ e' he' χX χW om r s r' s' hP Ψ hΨ)
  refine integral_tsum_of_bound μ 𝓕 (by simp [h1]) _ (fun w => ?_)
    (∑' w : Fin d₁ → E, ‖thetaSum F (e' (M₁.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F w)) (e₀ (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.x) (incV F H'.y)) Ψ))))‖)
    (fun u => ?_)
  · simp_rw [hℓ w]
    exact ((hψ.1.comp (hℓc w)).mul continuous_const).aestronglyMeasurable
  · simp_rw [hℓ _ u, norm_mul, GlobalTheory.StdCharFromIsStd.norm_psi hψ, one_mul]
    exact ⟨hS, le_rfl⟩

end GlobalTheory.ThKIsoSwap
