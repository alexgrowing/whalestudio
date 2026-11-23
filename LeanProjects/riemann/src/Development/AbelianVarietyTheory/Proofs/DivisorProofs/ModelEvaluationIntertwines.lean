import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingTrRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlanePairRestrictionFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardTraceAddCharIsStandardCharOfAdmissibleCM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesAdelicSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelEvaluationPreservesAdmissible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjLinEqOfEqOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorInverseLocalStatement

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval GlobalTheory.WeilTr

noncomputable section

namespace GlobalTheory.DblTr

theorem hasDbl_transp : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) →
    ∀ T : Fn F n d ≃ₗ[ℂ] Fn F n d, (∀ Φ ∈ schA F (Fin n × Fin d), T Φ = e Φ) →
    ∀ d' d₁' : Darboux (symp (cA σ) (-1) (incM F W.J) (incM F X.J)) (Fin n × Fin d),
      (∀ x : Matrix (Fin n) (Fin d) (AE F E), d'.e xᵀ = M.co.e x) → (∀ x : Matrix (Fin n) (Fin d) (AE F E), d₁'.e xᵀ = M₁.co.e x) →
      HasDbl (cA σ) (adeleClass F) B.ψ (-1) (incM F W.J) (incM F X.J) d' d₁' T := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e he hbij T hTe d' d₁' hd' hd₁'
  have hψ : ∀ t, ‖B.ψ t‖ = 1 := GlobalTheory.StdCharWeilDatum.norm_psi hpair.base.std
  have hL : IsLocOp e := isLocOp_of_isEv hpair.good hM₁ he
  obtain ⟨e', hL', hinv⟩ := GlobalTheory.T.local_operator_inverse_local e hL hbij
  have hTe' : ∀ Φ ∈ schA F (Fin n × Fin d), T.symm Φ = e' Φ := by
    intro Φ hΦ
    obtain ⟨Ψ, hΨ, rfl⟩ := hbij.surjOn hΦ
    rw [← hTe Ψ hΨ, LinearEquiv.symm_apply_apply, hTe Ψ hΨ, hinv Ψ hΨ]
  have hmem : ∀ Φ, Φ ∈ schA F (Fin n × Fin d) ↔ T Φ ∈ schA F (Fin n × Fin d) := by
    intro Φ
    constructor
    · intro h
      rw [hTe Φ h]
      exact hbij.mapsTo h
    · intro h
      obtain ⟨Ψ, hΨ, hΨe⟩ := hbij.surjOn h
      have h1 : T Ψ = T Φ := (hTe Ψ hΨ).trans hΨe
      rw [← T.injective h1]
      exact hΨ
  have hn : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
    rw [incM, Matrix.map_one _ (map_zero _) (map_one _)]
  have hd1 : (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ = 1 := by
    rw [incM, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  have Heisenberg₂ : ∀ w, ∀ Φ ∈ schA F (Fin n × Fin d), T (d'.rho B.ψ w Φ) = d₁'.rho B.ψ w (T Φ) := by
    intro w Φ hΦ
    have e1 : ∀ Ψ, d'.rho B.ψ w Ψ = M.co.rho B.ψ wᵀ Ψ := fun Ψ => by
      simp only [Darboux.rho]
      rw [← hd' wᵀ, Matrix.transpose_transpose]
    have e2 : ∀ Ψ, d₁'.rho B.ψ w Ψ = M₁.co.rho B.ψ wᵀ Ψ := fun Ψ => by
      simp only [Darboux.rho]
      rw [← hd₁' wᵀ, Matrix.transpose_transpose]
    have hρ : M.co.rho B.ψ wᵀ Φ ∈ schA F (Fin n × Fin d) :=
      GlobalTheory.SchrKeepsSchA.schr_mem_schA F B.ψ hpair.base.std _ _ Φ hΦ
    have h := he.Heisenberg₂ wᵀ Φ hΦ
    rw [hn, hd1, Matrix.one_mul, Matrix.mul_one] at h
    rw [e1, e2, hTe _ hρ, hTe Φ hΦ, h]
  have hunit : ∀ μ : @Measure (Fin n × Fin d → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ C : ℝ≥0∞, ∀ Φ ∈ schA F (Fin n × Fin d), ∫⁻ x, ‖T Φ x‖ₑ ^ 2 ∂μ = C * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
    intro μ hμ
    obtain ⟨C, hC⟩ := GlobalTheory.ModelTrUnit.exists_const hP F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e he hbij μ hμ
    exact ⟨C, fun Φ hΦ => by rw [hTe Φ hΦ]; exact hC Φ hΦ⟩
  exact hasDbl_of_loc (cA σ) (-1) (incM F W.J) (incM F X.J) B.ψ hψ d' d₁' T e e' hL hL' hTe hTe' hmem Heisenberg₂ hunit

end GlobalTheory.DblTr
