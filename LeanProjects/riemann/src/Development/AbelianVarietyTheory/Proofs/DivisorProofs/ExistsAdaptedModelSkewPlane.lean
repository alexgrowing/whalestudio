import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneZeroInsertionLinearApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneDarbouxCoordinatesExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneDarbouxCoordinatesCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalEvaluationSchwartzBruhatImageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicEvaluationPreservesSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneDarbouxEvaluationIdentityStatement

noncomputable section
namespace GlobalTheory.ThK.PlaneEv
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneEv

theorem incM_one' {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} :
    incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)

theorem evalZero_adapted : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ r s r' s' i₀ i₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (M : Model σ X W)
    (M₁ : Model σ X W₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    M₁.IsGood B.ψ →
    ∃ (Ma : Model σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n d₁), Ma.IsGood B.ψ ∧ IsEv B Ma M₁ 1 H'.ι (iso0 n H') e ∧
      ∃ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁))
        (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d₁ → Fv F v) → ℂ),
        (Ma.Pol B.ψ B.emb).map (ei : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d₁)) = M₁.Pol B.ψ B.emb ∧
        (∀ v, ev v (Ma.vac v) = M₁.vac v ∧ (SB _).map (ev v) = SB _) ∧
        ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = Ma.vac v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v) := by
  intro _ F E _ _ _ _ _ σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M M₁ hB hX hW hM hH hM₁
  have hd : d = d₁ + 2 := hH.rank
  obtain ⟨co, hco⟩ := GlobalTheory.T.adapted_plane_darboux_coordinates_exist F E σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M₁ hd hB hX hW hH hM₁
  obtain ⟨vac, hvac, hstd, hres⟩ := GlobalTheory.T.exists_vacuum_family_eventually_indicator_ev_eq F E σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M₁ hd hB hX hW hH hM₁ co hco
  have hpol := GlobalTheory.T.adapted_plane_darboux_evaluation_identity F E σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M₁ hd hB hX hW hH hM₁ co hco
  obtain ⟨hlow, hmulX, -, hrat⟩ := hco
  let Ma : Model σ X W := ⟨co, vac, M.μ, M.dom⟩
  have hev : ∀ (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) →
      (∀ᶠ v in cofinite, φ v = Ma.vac v) → evA F hd (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) =
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei F hd f) fun v => ev hd v (φ v) := fun f φ _ _ => evA_pure hd f φ
  have hloc : ∀ v, ev hd v (Ma.vac v) = M₁.vac v ∧ (SB _).map (ev hd v) = SB _ :=
    fun v => ⟨hres v, GlobalTheory.T.local_evaluation_schwartz_bruhat_image F n d d₁ hd v⟩
  refine ⟨Ma, evA F hd, ⟨hrat, hvac, hstd, hM.haar, hM.dom⟩, ⟨fun Φ hΦ => GlobalTheory.T.adelic_evaluation_preserves_schwartz F n d d₁ hd Φ hΦ, ?_, ?_,
    ⟨ei F hd, fun v => ev hd v, ei_ne_zero (F := F) hd, hloc, hev⟩⟩, ei F hd, fun v => ev hd v, hpol, hloc, hev⟩
  · intro z Φ _
    funext x
    simp only [evA_apply, Darboux.rho, schr, incM_one', Matrix.one_mul]
    rw [hlow z, ins0_dotProduct_ins0, ins0_dotProduct_ins0, ← ins0_add]
  · rintro u ⟨y, rfl⟩ Φ _
    funext x
    simp only [evA_apply, Darboux.rho, schr]
    have h0 : (fun p => (co.e (Matrix.vecMulVec y (incV F H'.x))).2 ((idx hd).symm (Sum.inl p))) = 0 :=
      funext (hmulX y).2
    rw [(hmulX y).1, ins0_dotProduct, h0, dotProduct_zero, zero_dotProduct, mul_zero, add_zero, add_zero,
      AddChar.map_zero_eq_one, one_mul]

end GlobalTheory.ThK.PlaneEv
