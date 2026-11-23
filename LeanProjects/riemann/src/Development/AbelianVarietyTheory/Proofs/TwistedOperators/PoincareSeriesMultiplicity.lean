import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesCoefficientsCuspidalIffOneSided
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsQuotHeightMulExpInfLe
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoefficientPoincareSeriesIsAutomorphicStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesSmoothModerateGrowthDerivStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesCuspidalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GkMapCuspFormsExtendsToSmoothVectors
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingLevelsAndStepsHaarMeasuresExist
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PoinMult

open GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension

open Classical in

theorem exists_multT_eq_poin : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.DiscreteSeriesCoefficientsCuspidal → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (Λ : Lat V) (𝔪 : Ideal (𝓞 D.host.E)), IsSelfDualC V Λ → 𝔪 ≠ ⊥ → ∀ (v : ∀ τ, M.H τ), KDecay M v → ∀ c : GA D V, Nonempty D.what₂.Tau → ∃ y ∈ MultT θ M (Lev.levA V (congLev D.sp.cm V.gram Λ 𝔪) : Set _) 1, ∀ a : M.Vec, (∀ τ, (a τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) → y (PiTensorProduct.tprod ℂ a) = poin θ M (congLev D.sp.cm V.gram Λ 𝔪) v c fun τ => a τ := by
  intro hHC hCW hDS hRD D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c hτ
  obtain ⟨haut, ⟨T₀, hT₀⟩, hKeq⟩ := GlobalTheory.T.coefficientPoincareSeries_isAutomorphic D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c
  have hder := GlobalTheory.T.poincareSeries_smooth_moderateGrowth_deriv hHC D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c
  have hcusp := GlobalTheory.T.poincare_series_cuspidal hDS D θ hθ V S M Λ 𝔪 hΛ h𝔪 v hv c hτ
  obtain ⟨vol⟩ := (GlobalTheory.Unf.VolExist.measures_exist D).1 V
  have hGK : IsGKMap θ M (Lev.levA V (congLev D.sp.cm V.gram Λ 𝔪) : Set _) 1 vol.μ vol.𝓕 T₀ := by
    refine ⟨fun u => ?_, fun u => ?_, fun u => ?_, fun u => ?_, fun u => ?_, fun u k hk g => ?_, ?_, ?_⟩
    · rw [hT₀]; exact (haut u).1
    · rw [hT₀]; exact (hder u).1
    · rw [hT₀]; exact hcusp u
    · rw [hT₀]
      have hr := GlobalTheory.Grow.rapidDec_of_unifModGrowth hRD hθ (haut u).1 (hder u).1 (hder u).2.1 (hcusp u)
      exact GlobalTheory.CuspDecay.memLp_of_bounded hr.continuous hr.bounded _ _ vol.haar vol.fund 2
    · rw [hT₀]; exact (hder u).2.1
    · rw [hT₀, (haut u).2.2.2 k hk g]; simp
    · intro τ k hk u w hw
      rw [hT₀, hT₀]
      have e : (fun τ' => ((Function.update u τ w τ' : kFin M τ') : M.H τ')) =
          Function.update (fun τ' => (u τ' : M.H τ')) τ (M.rep τ k (u τ)) := by
        funext τ'
        by_cases h : τ' = τ
        · subst h; simp [hw]
        · simp [Function.update_of_ne h]
      rw [e]
      exact hKeq _ τ k (maxCpt_subset M τ hk)
    · intro τ X hX u w hw
      rw [hT₀, hT₀]
      exact (hder u).2.2 τ X hX w hw
  obtain ⟨T, ⟨hTm, hTe⟩, -⟩ := (GlobalTheory.GKExtensionToSmoothVectors.gkExtension hHC hCW D).1 θ hθ V S M _ 1 vol.μ vol.𝓕 vol.haar vol.fund T₀ hGK
  refine ⟨PiTensorProduct.lift T, ?_, fun a ha => ?_⟩
  · rw [mem_multT, LinearEquiv.symm_apply_apply]
    exact Submodule.subset_span hTm
  · rw [PiTensorProduct.lift.tprod, hTe a (fun τ => ⟨a τ, ha τ⟩) (fun τ => rfl), hT₀]

end GlobalTheory.PoinMult

end
