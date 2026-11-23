import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLevi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingLeviTranslationIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigurationStabiliserMeasureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigurationStabiliserIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarStabilizerEvalConfigFirstStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzEqOfIntegralsEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryPreservesInnerProductStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ConeComm

theorem pair_cone : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')),
      ∀ φ ∈ schA F (Fin b × Fin (b + a')), ∀ μY : @Measure (Fin b × Fin (b + a') → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μY →
      ∫ y, cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) Ψ y * starRingEnd ℂ (φ y) ∂μY =
        ∫ k, ∫ l, (∫ y, e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Ψ)) y * starRingEnd ℂ (φ y) ∂μY) * (X.ν l : ℂ) *
          ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2) ∂μ ∂μK := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC e he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Ψ hΨ φ hφ μY hμY
  exact GlobalTheory.T.haar_stabilizer_eval_config_first hKP F E σ B b a' G G₁ H H' hC e he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Ψ hΨ φ hφ μY hμY
    (GlobalTheory.T.configuration_stabiliser_integral hKP F E σ B b a' G G₁ H H' hC e he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Ψ hΨ φ hφ μY hμY)

theorem cone_comm : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ (h₁ : UA σ G₁.W.J), ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')),
      om₁ (1, h₁) (cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) Ψ) =
        fun y => ∫ k, ∫ l, om₁ (1, h₁) (e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Ψ))) y * (X.ν l : ℂ) *
          ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2) ∂μ ∂μK := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC e he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ h₁ Ψ hΨ
  obtain ⟨m, hm⟩ := GlobalTheory.LeviUnitary.exists_isLevi hT.base hT.geo.hW hT₁.geo.hW hC.hH' h₁
  have hS := IsUWeilPair.isUSplitting hT.weil
  have hS₁ := IsUWeilPair.isUSplitting hT₁.weil
  have hΨ' : om (1, m) Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')) := hS.pres _ _ hΨ
  have hX : ∀ (k : K) l, G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Ψ) ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')) :=
    fun k l => GlobalTheory.HeisSchA.rho_mem_schA _ _ hT.base.std _ _ (hS.pres _ _ hΨ)
  have key : ∀ (k : K) l, om₁ (1, h₁) (e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Ψ))) =
      e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) (om (1, m) Ψ))) := by
    intro k l
    have h1 := GlobalTheory.ThK.evLaw_isoA hKP F E σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ 1 h₁ m hm _ (hX k l)
    simp at h1
    rw [← h1, hS.impl (1, m) _ _ (hS.pres _ _ hΨ)]
    have hact : actAB (cA σ) ((1 : UA σ G.V.J), m) (shiftA H H' l) = shiftA H H' l := by
      have hy := hm.2.1
      simp only [inv_one, Units.val_one, map_one, one_smul] at hy
      unfold actAB shiftA
      simp only [Prod.fst, Prod.snd, OneMemClass.coe_one, Units.val_one, Matrix.one_mul, Matrix.smul_mul]
      congr 1
      ext i j
      simp only [Matrix.vecMulVec, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply]
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      congr 1
      have := congrFun hy j
      simp only [Matrix.mulVec, dotProduct] at this
      rw [← this]
      exact Finset.sum_congr rfl fun x _ => mul_comm _ _
    have hcomm : om (1, m) (om (k.1, 1) Ψ) = om (k.1, 1) (om (1, m) Ψ) := by
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      ext <;> simp
    rw [hact, hcomm]
  have hR : (fun y => ∫ k : K, ∫ l, om₁ (1, h₁) (e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Ψ))) y * (X.ν l : ℂ) *
      ((absE F E l : ℝ) : ℂ) ^ ((b + 2 - a') / 2) ∂μ ∂μK) =
      cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (om (1, m) Ψ) := by
    funext y
    simp only [key]
    rfl
  rw [hR]
  have hc := GlobalTheory.T.configuration_stabiliser_measure hKP F E σ B b a' G G₁ H H' hC e he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Ψ hΨ
  have hc' := GlobalTheory.T.configuration_stabiliser_measure hKP F E σ B b a' G G₁ H H' hC e he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ _ hΨ'
  have hU : ∀ μY : @Measure (Fin b × Fin (b + a') → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μY →
      ∀ φ ∈ schA F (Fin b × Fin (b + a')), ∫⁻ x, ‖om₁ (1, h₁) φ x‖ₑ ^ 2 ∂μY = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μY :=
    fun μY hμY φ hφ => hS₁.unit μY hμY (1, h₁) φ hφ
  have hP := GlobalTheory.T.unitary_preserves_inner_product F _ (om₁ (1, h₁)) (fun φ hφ => hS₁.pres _ φ hφ) hU
  refine GlobalTheory.T.schwartz_eq_of_integrals_eq F _ _ (hS₁.pres _ _ hc) _ hc' fun μY hμY ψ hψ => ?_
  have hφ : om₁ (1, h₁⁻¹) ψ ∈ schA F (Fin b × Fin (b + a')) := hS₁.pres _ _ hψ
  have hψφ : om₁ (1, h₁) (om₁ (1, h₁⁻¹) ψ) = ψ := by
    rw [← Module.End.mul_apply, ← map_mul, show ((1 : UA σ G₁.V.J), h₁) * (1, h₁⁻¹) = 1 from
      Prod.ext (mul_one _) (mul_inv_cancel h₁), map_one, Module.End.one_apply]
  rw [← hψφ, hP μY hμY _ hc _ hφ,
    pair_cone hKP F E σ B b a' G G₁ H H' hC e he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Ψ hΨ _ hφ μY hμY,
    pair_cone hKP F E σ B b a' G G₁ H H' hC e he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ _ hΨ' _ (hS₁.pres _ _ hφ) μY hμY]
  refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun l => ?_)
  simp only
  rw [← key k l, hP μY hμY _ (he.maps _ (hX k l)) _ hφ]

end GlobalTheory.ConeComm
