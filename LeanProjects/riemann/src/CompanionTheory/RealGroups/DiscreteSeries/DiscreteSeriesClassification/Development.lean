import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.InConeRefl
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.PsiFor
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExistsMu
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KTypesAboveOfDsClass
import CompanionTheory.AutomorphicTheory.TemperedLocalSpectra.DiscreteSeriesSU.GapInv

noncomputable section

namespace CompanionTheory.RgDs

open ReciprocityTheory.ChartRestriction.DS

theorem model_of (hL : ExplicitFunctionSquareIntegrable) (hK : Key) (hH : Hilb) {n : ℕ} (ε : Fin n → Bool) (lam : Fin n → ℝ)
    (hl : Formalism.QuantumDeterminants.IsHCParam lam) :
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.MainNotions.S.IsDS ε lam σ ∧
        ∀ (η : Fin n → ℝ) (S : Submodule ℂ H), Formalism.MainNotions.S.IsKTypeOf ε σ η S → InCone (lowK ε lam) η := by
  obtain ⟨T⟩ := HW.kType_exists ε lam hl
  obtain ⟨μ, hμ⟩ := S7.exists_mu hl
  have hP : IsPsiFor ε lam T (S7.PsiM T μ) :=
    ⟨fun k₁ k₂ g hg => S7.psiM_equiv T μ k₁ k₂ hg, S7.psiM_one T μ, S7.psiM_smooth T μ hμ,
      fun g hg => S7.psiM_casimir T μ hμ hg, hL n ε lam T μ hl hμ⟩
  exact ⟨_, inferInstance, inferInstance, _, hH n ε lam T _ hl hP (hK n ε lam T μ hl hμ hP)⟩

theorem dsExists_of (hL : ExplicitFunctionSquareIntegrable) (hK : Key) (hH : Hilb) : GlobalTheory.Dec.DSExists := by
  intro n ε lam hl
  obtain ⟨H, _, _, σ, h, -⟩ := model_of hL hK hH ε lam hl
  exact ⟨H, _, _, σ, h⟩

theorem kTypesAbove_of (hL : ExplicitFunctionSquareIntegrable) (hK : Key) (hH : Hilb) : GlobalTheory.Dec.KTypesAbove := by
  intro n ε lam H _ _ σ hl hσ μ S hS
  obtain ⟨G, _, _, π, hπ, hc⟩ := model_of hL hK hH ε lam hl
  obtain ⟨S', hS'⟩ := GlobalTheory.LowestKTypeDetermines.exists_ktype_of_uEquiv
    (CompanionTheory.DiscreteSeriesGap.GapInv.dsUnique_dec n ε lam H σ G π hl hσ hπ) ⟨S, hS⟩
  exact hc μ S' hS'

end CompanionTheory.RgDs
