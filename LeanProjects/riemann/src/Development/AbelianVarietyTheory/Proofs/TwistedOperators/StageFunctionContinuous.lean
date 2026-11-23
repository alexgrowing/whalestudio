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

theorem stageFun_continuous : ∀ {n : ℕ} {ε : Fin n → Bool} {U V : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (M : Subgroup (UJ ε)) (Fsp : Submodule ℂ (UJ ε → U)) (ι : Fsp →ₗ[ℂ] V) (μ : Measure ↥(KG ε ⊓ M)) [IsProbabilityMeasure μ], (∀ f : Fsp, ‖ι f‖ ^ 2 = ∫ k : ↥(KG ε ⊓ M), ‖f.1 k‖ ^ 2 ∂μ) → ∀ {F : UJ ε → U}, Continuous F → (∀ g, restr M F g ∈ Fsp) → Continuous (stageFun M Fsp ι F) := by
  intro n ε U V _ _ _ _ M Fsp ι μ _ hnorm F hF hmem

  let Φ : C(UJ ε, C(KG ε, U)) :=
    ContinuousMap.curry ⟨fun p : UJ ε × KG ε => F ((p.2 : UJ ε) * p.1), by fun_prop⟩
  have hΦ : ∀ g (k : KG ε), Φ g k = F ((k : UJ ε) * g) := fun g k => rfl
  have key : ∀ g g₀, ‖stageFun M Fsp ι F g - stageFun M Fsp ι F g₀‖ ≤ ‖Φ g - Φ g₀‖ := by
    intro g g₀
    rw [stageFun_of_mem ι (hmem g), stageFun_of_mem ι (hmem g₀), ← map_sub]
    set f : Fsp := (⟨_, hmem g⟩ - ⟨_, hmem g₀⟩ : Fsp) with hf
    set C := ‖Φ g - Φ g₀‖
    have hC : 0 ≤ C := norm_nonneg _
    have hpt : ∀ k : ↥(KG ε ⊓ M), ‖f.1 k‖ ^ 2 ≤ C ^ 2 := by
      intro k
      have hkM : (k : UJ ε) ∈ M := (Subgroup.mem_inf.1 k.2).2
      have hkK : (k : UJ ε) ∈ KG ε := (Subgroup.mem_inf.1 k.2).1
      have : f.1 k = (Φ g - Φ g₀) ⟨k, hkK⟩ := by
        simp only [hf, Submodule.coe_sub, Pi.sub_apply, ContinuousMap.sub_apply, hΦ,
          restr_of_mem _ _ hkM]
      rw [this]
      exact pow_le_pow_left₀ (norm_nonneg _) (ContinuousMap.norm_coe_le_norm _ _) 2
    have hint : ∫ k : ↥(KG ε ⊓ M), ‖f.1 k‖ ^ 2 ∂μ ≤ C ^ 2 := by
      have h1 := norm_integral_le_of_norm_le_const (μ := μ) (f := fun k => ‖f.1 k‖ ^ 2) (C := C ^ 2)
        (Filter.Eventually.of_forall fun k => by
          rw [Real.norm_of_nonneg (by positivity)]; exact hpt k)
      simp at h1
      exact (le_abs_self _).trans h1
    have h3 : ‖ι f‖ ^ 2 ≤ C ^ 2 := (hnorm f).symm ▸ hint
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hC two_ne_zero).1 h3
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun g => key g g₀) ?_
  have : Filter.Tendsto (fun g => Φ g - Φ g₀) (nhds g₀) (nhds 0) := by
    simpa using ((Φ.continuous.tendsto g₀).sub_const (Φ g₀))
  simpa using this.norm

end GlobalTheory.RealInd.Stages
