import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IoInjective
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SkewOfCommute
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MeanValueIneqRightTranslateRealPointNearOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSobolevInequalityAdelicUnitary
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory Matrix
open scoped TensorProduct Topology InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.HCCusp.RealLog

theorem exists_small_log : ∀ (D : D7) (θ : GlobalTheory.Mem.Th.InfF D), IsInfFam θ → ∀ (V : HSp D) (δ : ℝ), 0 < δ →
    ∃ N ∈ 𝓝 (1 : GA D V), ∀ r ∈ N, r ∈ GinfC V →
      ∃ X : GlobalTheory.SmoothForms.LieN V, ‖X‖ < δ ∧ GlobalTheory.SmoothForms.expInf θ V X = r := by
  intro D θ hθ V δ hδ
  have R : GlobalTheory.SmoothForms.RealPoints θ V := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  obtain ⟨δ₁, C, hδ₁, hC, hlog⟩ := GlobalTheory.CuspGeo.MeanValue.exists_log hθ R
  set ε : ℝ := min δ₁ (δ / (2 * (C + 1))) with hε
  have hε0 : 0 < ε := lt_min hδ₁ (by positivity)
  have hCε : C * ε < δ := by
    have h1 : ε ≤ δ / (2 * (C + 1)) := min_le_right _ _
    have h2 : C * ε ≤ C * (δ / (2 * (C + 1))) := mul_le_mul_of_nonneg_left h1 hC
    have h3 : C * (δ / (2 * (C + 1))) < δ := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    exact lt_of_le_of_lt h2 h3
  have hcont : ∀ τ, Continuous fun g : GA D V => infMat D.sp.cm.sig V.gram (θ τ) g := by
    intro τ
    have hc := GlobalTheory.SobLoc.continuous_arch (θ := θ) hθ V τ
    simpa only [Formalism.IndefR.FWT.archM_eq] using hc
  have hone : ∀ τ, infMat D.sp.cm.sig V.gram (θ τ) (1 : GA D V) = 1 :=
    fun τ => R.2.2.2.2.1 1 (one_mem _) τ
  refine ⟨⋂ τ, ⋂ i, ⋂ j, {g : GA D V | ‖(infMat D.sp.cm.sig V.gram (θ τ) g - 1) i j‖ < ε}, ?_, ?_⟩
  · refine Filter.iInter_mem.2 fun τ => Filter.iInter_mem.2 fun i => Filter.iInter_mem.2 fun j => ?_
    refine IsOpen.mem_nhds ?_ ?_
    · exact isOpen_lt (((hcont τ).sub continuous_const).matrix_elem i j).norm continuous_const
    · simp only [Set.mem_ofPred_eq, hone, sub_self, Matrix.zero_apply, norm_zero]
      exact hε0
  · intro r hr hrinf
    simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hr
    have hclose : GlobalTheory.CuspGeo.CloseR θ V r ε := ⟨hrinf, fun τ i j => (hr τ i j).le⟩
    obtain ⟨Z, hZ, hn⟩ := hlog r ε hε0.le (min_le_left _ _) hclose
    exact ⟨Z, lt_of_le_of_lt hn hCε, hZ⟩

end GlobalTheory.CompanionTheory.HCCusp.RealLog

end
