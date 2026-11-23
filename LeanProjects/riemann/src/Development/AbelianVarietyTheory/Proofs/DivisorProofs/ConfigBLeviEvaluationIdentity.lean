import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEvaluationZeroConeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSecondVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneFirstVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSchrodingerModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharactersRestrictionEta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBTripleEvaluationCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBIntermediateModelEvaluation
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK.LeviLawB

theorem levi_law : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b)
    (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' →
      ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
      ∀ g₀ g, IsLevi H 1 g₀ g → ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))),
        e' (om' (g, 1) Ψ) = om₁' (g₀, 1) (e' Ψ) := by
  intro hK F E _ _ _ _ _ σ B a b G G₁ H H' hC e' he' X om om' om₁ om₁' hT hT₁ g₀ g hg Ψ hΨ
  have pV' := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).2
  have p1 := (GlobalTheory.ThK.Check.isPair_of_isTriple hT₁).2
  obtain ⟨Mm, hMm⟩ := GlobalTheory.ModelEx.model_exists F E σ B pV'.base b (a + (b + 2)) G₁.V' G.W _ _ _ _ p1.herm pV'.skew
  obtain ⟨omm, hom⟩ := GlobalTheory.WeilExGen.exists_isWeil hK F E σ B pV'.base b (a + (b + 2)) G₁.V' G.W _ _ _ _ p1.herm pV'.skew Mm hMm
    X.α (X.α / X.β) pV'.hX pV'.hW p1.resX pV'.resW
  have pm : IsPair B Mm X.α (X.α / X.β) omm _ _ _ _ :=
    ⟨pV'.base, p1.herm, pV'.skew, hMm, pV'.hX, pV'.hW, p1.resX, pV'.resW, hom⟩
  obtain ⟨⟨e₁, he₁⟩, law₁⟩ := GlobalTheory.T.adapted_plane_first_variable hK F E σ B _ _ G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ pV' b G₁.V' H 0 (b + 1)
    Mm omm _ _ hC.hH pm
  obtain ⟨e₂, he₂⟩ := ((GlobalTheory.T.theta_evaluation_zero_cone hK).1 F E σ B _ _ G₁.V' G.W Mm X.α (X.α / X.β) omm _ _ _ _ pm (a + b) G₁.V' G₁.W H'
    a (a + b + 1) G₁.M' rfl hC.hH' hT₁.geo.hM').1
  have pres : ∀ (p : UA σ G.V'.J × UA σ G.W.J), ∀ Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))),
      om' p Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))) :=
    fun p Φ hΦ => (IsUWeilPair.isUSplitting hT.weil').pres p Φ hΦ

  have hlaw : ∀ Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))), e₂ (e₁ (om' (g, 1) Φ)) = om₁' (g₀, 1) (e₂ (e₁ Φ)) := by
    intro Φ hΦ
    have k1 := law₁ e₁ he₁ 1 1 g₀ g hg 1 (one_mem _) Φ hΦ
    have k2 := GlobalTheory.T.adapted_plane_second_variable hK F E σ B _ _ G₁.V' G.W Mm X.α (X.α / X.β) omm _ _ _ _ pm (a + b) G₁.W H' a (a + b + 1) G₁.M' om₁'
      _ _ hC.hH' p1 e₂ he₂ g₀ 1 1 1 (GlobalTheory.ThK.Check.isLevi_one H') 1 (one_mem _) (e₁ Φ) (he₁.maps Φ hΦ)
    simp only [mul_one, one_mul, map_one, Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_smul] at k1 k2
    rw [k1, k2]

  have one : incM F (1 : Matrix (Fin b) (Fin b) E) = 1 := GlobalTheory.ThK.Check.incM_one
  have one' : incM F (1 : Matrix (Fin (a + (b + 2))) (Fin (a + (b + 2))) E) = 1 := GlobalTheory.ThK.Check.incM_one
  have hmaps : ∀ Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))), (e₂ ∘ₗ e₁) Φ ∈ schA F (Fin b × Fin (a + b)) :=
    fun Φ hΦ => he₂.maps _ (he₁.maps Φ hΦ)
  have hheis : ∀ z, ∀ Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))),
      (e₂ ∘ₗ e₁) (G.M'.co.rho B.ψ (incM F H.ι * z * (incM F H'.ι)ᵀ) Φ) = G₁.M'.co.rho B.ψ z ((e₂ ∘ₗ e₁) Φ) := by
    intro z Φ hΦ
    have k1 := he₁.Heisenberg₂ (z * (incM F H'.ι)ᵀ) Φ hΦ
    rw [one', Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc] at k1
    have k2 := he₂.Heisenberg₂ z (e₁ Φ) (he₁.maps Φ hΦ)
    rw [one, Matrix.one_mul] at k2
    simp only [LinearMap.comp_apply]
    rw [k1, k2]
  have hinv : ∀ u ∈ isoB H H', ∀ Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))),
      (e₂ ∘ₗ e₁) (G.M'.co.rho B.ψ u Φ) = (e₂ ∘ₗ e₁) Φ := by
    intro u hu Φ hΦ
    simp only [LinearMap.comp_apply]
    rcases hu with ⟨z, rfl⟩ | ⟨y, rfl⟩
    · rw [he₁.inv _ ⟨z, rfl⟩ Φ hΦ]
    · have k1 := he₁.Heisenberg₂ (Matrix.vecMulVec y (incV F H'.x)) Φ hΦ
      rw [one', Matrix.transpose_one, Matrix.mul_one, Matrix.mul_vecMulVec] at k1
      rw [k1, he₂.inv _ ⟨y, rfl⟩ _ (he₁.maps Φ hΦ)]
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
      have hc' : ∀ᶠ v in cofinite, ev₁ v (φ v) = Mm.vac v := by
        filter_upwards [hc] with v hv; rw [hv, (hv₁ v).1]
      simp only [LinearMap.comp_apply, ContinuousLinearMap.comp_apply]
      rw [hl₁ f φ hφ hc, hl₂ _ _ hφ' hc']

  obtain ⟨c, hc⟩ := GlobalTheory.T.config_b_triple_evaluation_compatible hK F E σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ e' he' (e₂ ∘ₗ e₁) hmaps hheis hinv hloc
  obtain ⟨Φ₀, hΦ₀, hne⟩ := GlobalTheory.ThK.EvCompNe.comp_ne_zero hK F E σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ Mm hMm e₁ he₁ e₂ he₂
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hne
    have := hc Φ₀ hΦ₀
    simpa using this
  have he'E : ∀ Φ ∈ schA F (Fin (b + 2) × Fin (a + (b + 2))), e' Φ = c⁻¹ • e₂ (e₁ Φ) := by
    intro Φ hΦ
    have := hc Φ hΦ
    simp only [LinearMap.comp_apply] at this
    rw [this, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  rw [he'E _ (pres _ Ψ hΨ), hlaw Ψ hΨ, he'E Ψ hΨ, map_smul]

end GlobalTheory.ThK.LeviLawB
