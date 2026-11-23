import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEvaluationZeroConeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneFirstVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSchrodingerModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharactersRestrictionEta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBTripleEvaluationCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBIntermediateModelEvaluation

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK.EvUnipB

theorem incM_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) :
    incM F (1 : Matrix (Fin n) (Fin n) E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem unip_inv : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ u ∈ unip σ G.V' H, ∀ Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))), e' (om' (u, 1) Φ) = e' Φ := by
  intro hP F E _ _ _ _ _ σ B a b G G₁ H H' cfg e' hev X om om' om₁ om₁' T T₁ u hu Φ hΦ
  have P' := GlobalTheory.ThK.Inhab.pairV' T
  have P₁' := GlobalTheory.ThK.Inhab.pairV' T₁

  obtain ⟨Ma, hMa⟩ := GlobalTheory.ModelEx.model_exists F E σ B T.base b (a + (b + 2)) G₁.V' G.W _ _ _ _ P₁'.herm P'.skew
  obtain ⟨oma, hwa⟩ := GlobalTheory.WeilExGen.exists_isWeil hP F E σ B T.base b (a + (b + 2)) G₁.V' G.W _ _ _ _ P₁'.herm P'.skew Ma hMa
    X.α (X.α / X.β) P₁'.hX P'.hW P₁'.resX P'.resW
  have Pa : IsPair B Ma X.α (X.α / X.β) oma _ _ _ _ :=
    ⟨T.base, P₁'.herm, P'.skew, hMa, P₁'.hX, P'.hW, P₁'.resX, P'.resW, hwa⟩

  obtain ⟨⟨e₁, he₁⟩, law₁⟩ := GlobalTheory.T.adapted_plane_first_variable hP F E σ B (b + 2) (a + (b + 2)) G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ P'
    b G₁.V' H 0 (b + 1) Ma oma _ _ cfg.hH Pa
  obtain ⟨e₂, he₂⟩ := ((GlobalTheory.T.theta_evaluation_zero_cone hP).1 F E σ B b (a + (b + 2)) G₁.V' G.W Ma X.α (X.α / X.β) oma _ _ _ _ Pa
    (a + b) G₁.V' G₁.W H' a (a + b + 1) G₁.M' rfl cfg.hH' T₁.geo.hM').1

  have hmaps : ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))), (e₂ ∘ₗ e₁) Ψ ∈ schA F (Fin b × Fin (a + b)) :=
    fun Ψ hΨ => he₂.maps _ (he₁.maps Ψ hΨ)
  have heisC : ∀ (z : Matrix (Fin b) (Fin (a + b)) (AE F E)), ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))),
      (e₂ ∘ₗ e₁) (G.M'.co.rho B.ψ (incM F H.ι * z * (incM F H'.ι)ᵀ) Ψ) = G₁.M'.co.rho B.ψ z ((e₂ ∘ₗ e₁) Ψ) := by
    intro z Ψ hΨ
    have h1 := he₁.Heisenberg₂ (z * (incM F H'.ι)ᵀ) Ψ hΨ
    have h2 := he₂.Heisenberg₂ z (e₁ Ψ) (he₁.maps Ψ hΨ)
    rw [incM_one, Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc] at h1
    rw [incM_one, Matrix.one_mul] at h2
    simp only [LinearMap.comp_apply]
    rw [h1, h2]
  have invC : ∀ v ∈ isoB H H', ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))),
      (e₂ ∘ₗ e₁) (G.M'.co.rho B.ψ v Ψ) = (e₂ ∘ₗ e₁) Ψ := by
    intro v hv Ψ hΨ
    simp only [LinearMap.comp_apply]
    rcases hv with hv | ⟨y, rfl⟩
    · rw [he₁.inv v hv Ψ hΨ]
    · have h1 := he₁.Heisenberg₂ (Matrix.vecMulVec y (incV F H'.x)) Ψ hΨ
      rw [incM_one, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_vecMulVec] at h1
      rw [h1, he₂.inv _ ⟨y, rfl⟩ _ (he₁.maps Ψ hΨ)]
  have hloc : ∃ (ei : SInf F (Fin (b + 2) × Fin (a + (b + 2))) →L[ℂ] SInf F (Fin b × Fin (a + b)))
      (ev : ∀ v : Pl F, ((Fin (b + 2) × Fin (a + (b + 2)) → Fv F v) → ℂ) →ₗ[ℂ] (Fin b × Fin (a + b) → Fv F v) → ℂ),
      (∀ v, ev v (G.M'.vac v) = G₁.M'.vac v ∧ (SB _).map (ev v) = SB _) ∧
      ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = G.M'.vac v) →
        (e₂ ∘ₗ e₁) (pure f φ) = pure (ei f) fun v => ev v (φ v) := by
    obtain ⟨ei₁, ev₁, -, hv₁, hl₁⟩ := he₁.loc
    obtain ⟨ei₂, ev₂, -, hv₂, hl₂⟩ := he₂.loc
    refine ⟨ei₂.comp ei₁, fun v => (ev₂ v).comp (ev₁ v), fun v => ⟨?_, ?_⟩, fun f φ hφ hc => ?_⟩
    · simp [(hv₁ v).1, (hv₂ v).1]
    · rw [Submodule.map_comp, (hv₁ v).2, (hv₂ v).2]
    · have hφ' : ∀ v, ev₁ v (φ v) ∈ SB _ := fun v => by
        rw [← (hv₁ v).2]; exact Submodule.mem_map_of_mem (hφ v)
      have hc' : ∀ᶠ v in cofinite, ev₁ v (φ v) = Ma.vac v := by
        filter_upwards [hc] with v hv; rw [hv, (hv₁ v).1]
      simp only [LinearMap.comp_apply, ContinuousLinearMap.comp_apply]
      rw [hl₁ f φ hφ hc, hl₂ _ _ hφ' hc']

  obtain ⟨c, hc⟩ := GlobalTheory.T.config_b_triple_evaluation_compatible hP F E σ B a b G G₁ H H' cfg X om om' om₁ om₁' T T₁ e' hev (e₂ ∘ₗ e₁) hmaps heisC invC hloc
  obtain ⟨Φ₀, hΦ₀, hne⟩ := GlobalTheory.ThK.EvCompNe.comp_ne_zero hP F E σ B a b G G₁ H H' cfg X om om' om₁ om₁' T T₁ Ma hMa e₁ he₁ e₂ he₂
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hne
    have := hc Φ₀ hΦ₀
    rw [zero_smul, LinearMap.comp_apply] at this
    exact this
  have hpres : om' (u, 1) Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))) := (T.weil'.isUSplitting).pres _ _ hΦ
  have hLX : IsLevi (W₁ := G₁.V') H 1 (1 : UA σ G₁.V'.J) (1 : UA σ G.V'.J) := by
    refine ⟨?_, ?_, ?_⟩
    · show (1 : Matrix _ _ _) *ᵥ _ = _
      simp
    · show (1 : Matrix _ _ _) *ᵥ _ = _
      simp
    · show (1 : Matrix _ _ _) * _ = _ * (1 : Matrix _ _ _)
      simp

  have key : e₂ (e₁ (om' (u, 1) Φ)) = e₂ (e₁ Φ) := by
    have h1 := law₁ e₁ he₁ 1 1 1 1 hLX u hu Φ hΦ
    simp only [mul_one, map_one, Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_smul] at h1
    rw [h1, show ((1 : UA σ G₁.V'.J), (1 : UA σ G.W.J)) = 1 from rfl, map_one, Module.End.one_apply]
  calc e' (om' (u, 1) Φ) = c⁻¹ • (c • e' (om' (u, 1) Φ)) := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]
    _ = c⁻¹ • (c • e' Φ) := by
        rw [← hc _ hpres, ← hc _ hΦ]
        simp only [LinearMap.comp_apply]
        rw [key]
    _ = e' Φ := by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]

end GlobalTheory.ThK.EvUnipB

end
