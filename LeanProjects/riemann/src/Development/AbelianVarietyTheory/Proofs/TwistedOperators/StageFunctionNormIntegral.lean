import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrOfNotMem
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

namespace GlobalTheory.RealInd.Stages

theorem stageFun_normSq_integral : ∀ {n : ℕ} {ε : Fin n → Bool} {U V : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (M : Subgroup (UJ ε)) (Fsp : Submodule ℂ (UJ ε → U)) (ι : Fsp →ₗ[ℂ] V) (μ : Measure ↥(KG ε ⊓ M)) [IsProbabilityMeasure μ], (∀ f : Fsp, ‖ι f‖ ^ 2 = ∫ k : ↥(KG ε ⊓ M), ‖f.1 k‖ ^ 2 ∂μ) → ∀ {F : UJ ε → U}, Continuous F → (∀ g, restr M F g ∈ Fsp) → ∫ k : KG ε, ‖stageFun M Fsp ι F k‖ ^ 2 ∂muK ε = ∫ k : KG ε, ‖F k‖ ^ 2 ∂muK ε := by
  intro n ε U V _ _ _ _ M Fsp ι μ _ hnorm F hFc hF

  have h1 : ∀ k : KG ε, ‖stageFun M Fsp ι F k‖ ^ 2 = ∫ c : ↥(KG ε ⊓ M), ‖F ((c : UJ ε) * (k : UJ ε))‖ ^ 2 ∂μ := by
    intro k
    rw [stageFun_of_mem ι (hF k), hnorm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun c => ?_)
    simp only
    rw [restr_of_mem F (k : UJ ε) (Subgroup.mem_inf.1 c.2).2]
  simp_rw [h1]

  have hKc : Continuous fun k : KG ε => F (k : UJ ε) := hFc.comp continuous_subtype_val
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hKc.continuousOn
  have hint : Integrable (Function.uncurry fun (k : KG ε) (c : ↥(KG ε ⊓ M)) => ‖F ((c : UJ ε) * (k : UJ ε))‖ ^ 2)
      ((muK ε).prod μ) := by
    refine Integrable.of_bound (C := C ^ 2) ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      refine (continuous_norm.comp (hFc.comp ?_)).pow 2
      exact (continuous_subtype_val.comp continuous_snd).mul (continuous_subtype_val.comp continuous_fst)
    · refine Filter.Eventually.of_forall fun p => ?_
      have hp : (p.2 : UJ ε) * (p.1 : UJ ε) ∈ KG ε := mul_mem (Subgroup.mem_inf.1 p.2.2).1 p.1.2
      have hb := hC (⟨_, hp⟩ : KG ε) (Set.mem_univ _)
      simp only [Function.uncurry, Real.norm_eq_abs, abs_pow, abs_norm]
      exact pow_le_pow_left₀ (norm_nonneg _) hb 2
  rw [integral_integral_swap hint]
  have h3 : ∀ c : ↥(KG ε ⊓ M), ∫ k : KG ε, ‖F ((c : UJ ε) * (k : UJ ε))‖ ^ 2 ∂muK ε =
      ∫ k : KG ε, ‖F k‖ ^ 2 ∂muK ε := by
    intro c
    exact integral_mul_left_eq_self (μ := muK ε) (fun k : KG ε => ‖F (k : UJ ε)‖ ^ 2)
      (⟨c, (Subgroup.mem_inf.1 c.2).1⟩ : KG ε)
  simp_rw [h3]
  simp

end GlobalTheory.RealInd.Stages
