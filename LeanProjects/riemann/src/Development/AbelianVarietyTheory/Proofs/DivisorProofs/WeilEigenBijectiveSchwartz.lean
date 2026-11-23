import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerPreservesSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingTrRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerPreservesAdelicSchwartzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenBijectiveGoodModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenBijectivePairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenBijectivePairedModelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenBijectiveRegularStatement

noncomputable section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

theorem GlobalTheory.ModelTr.exists_isWeil_trans_of_bijOn : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ M₁ : Model σ X W, M₁.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, IsEv B M M₁ 1 1 ∅ e → Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) → ∃ om₁ : Rep σ X W, M₁.IsWeil B.ψ χX χW om₁ ∧ ∀ x, ∀ Φ ∈ schA F (Fin n × Fin d), e (om x Φ) = om₁ x (e Φ) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij
  obtain ⟨T, hTe, hTs⟩ := GlobalTheory.ModelTr.extEquiv (schA F (Fin n × Fin d)) e hbij
  have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h1' : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hgood : IsGoodInt (adeleClass F) B.ψ M.co M₁.co T := by
    refine ⟨hTs, fun w Φ hΦ => ?_, fun l => ?_, fun μ hμ => ?_⟩
    · have hm : M.co.rho B.ψ w Φ ∈ schA F (Fin n × Fin d) :=
        GlobalTheory.T.schroedinger_preserves_adelic_schwartz F B.ψ hpair.base.std _ (M.co.e w) Φ hΦ
      have := hev.Heisenberg₂ w Φ hΦ
      rw [h1, h1', Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one] at this
      rw [hTe _ hm, hTe _ hΦ, this]
    · refine (GlobalTheory.T.weil_eigen_bijective_good_model F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij l).trans (GlobalTheory.ModelTr.adm_congr ?_)
      intro Φ hΦ
      simp [hTe Φ hΦ]
    · obtain ⟨c, hc⟩ := GlobalTheory.T.weil_eigen_bijective_pair F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij μ hμ
      exact ⟨c, fun Φ hΦ => by rw [hTe Φ hΦ]; exact hc Φ hΦ⟩
  refine ⟨trRep T om, isUWeilPair_trRep hgood
    (GlobalTheory.T.weil_eigen_bijective_paired_models F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij T hTe)
    (GlobalTheory.T.weil_eigen_bijective_regular F E σ B n d X W M χX χW om r s r' s' hpair M₁ hM₁ e hev hbij T hTe) hpair.weil, fun x Φ hΦ => ?_⟩
  have hpres : om x Φ ∈ schA F (Fin n × Fin d) := hpair.weil.isUSplitting.pres x Φ hΦ
  rw [trRep_apply, ← hTe Φ hΦ, LinearEquiv.symm_apply_apply, hTe _ hpres]

end
