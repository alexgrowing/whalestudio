import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleCoefficientsAnalytic
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IrreducibleUnitaryAdmissible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientExistence
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableMatrixCoeffCyclicSpanStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableMatrixCoeffKAverageRightStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableMatrixCoeffKAverageLeftStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKProjectorFiniteDimStatement

noncomputable section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate
namespace GlobalTheory.TempKFin

theorem isTemperedKFin_of_isTempered : GlobalTheory.Published.IrreducibleUnitaryAdmissible → ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Measure (UJ ε)) [μ.IsHaarMeasure] (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U] (π : UJ ε →* (U →L[ℂ] U)), IsUnitaryRep π → IsTopIrreducible π → GlobalTheory.Orb.IsTempered μ π → IsTemperedKFin ε μ π := by
  intro hadm n ε μ _ U _ _ _ π hπ hirr ⟨v, hv0, hv⟩ S hS hSK s hs s' hs' e he
  obtain ⟨φ, hφc, hφS, hφR⟩ := GlobalTheory.T.exists_K_projector_finite_dim hadm n ε U π hπ hirr S hS hSK
  set D : Submodule ℂ U := Submodule.span ℂ (Set.range fun g => π g v) with hD
  have hDdense : D.topologicalClosure = ⊤ := by
    have hinv : ∀ g, ∀ w ∈ D.topologicalClosure, π g w ∈ D.topologicalClosure := by
      intro g w hw
      have hmap : ∀ x ∈ (D : Set U), π g x ∈ (D : Set U) := by
        intro x hx
        have hle : D ≤ D.comap ((π g : U →L[ℂ] U) : U →ₗ[ℂ] U) := by
          rw [hD, Submodule.span_le]
          rintro _ ⟨h, rfl⟩
          exact Submodule.subset_span ⟨g * h, by simp [map_mul]⟩
        exact hle hx
      have hw' : w ∈ closure (D : Set U) := by rwa [← Submodule.topologicalClosure_coe]
      rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
      exact map_mem_closure (π g).continuous hw' hmap
    rcases hirr.2 D.topologicalClosure ⟨D.isClosed_topologicalClosure, hinv⟩ with h | h
    · exfalso
      apply hv0
      have : v ∈ D.topologicalClosure := D.le_topologicalClosure (Submodule.subset_span ⟨1, by simp⟩)
      rw [h] at this
      exact (Submodule.mem_bot ℂ).1 this
    · exact h
  have hint : ∀ u : U, Integrable (fun k : KG ε => φ k • π k u) (muK ε) := fun u =>
    (hφc.smul ((hπ.continuous_apply u).comp continuous_subtype_val)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  let T : U →ₗ[ℂ] U :=
    { toFun := fun u => ∫ k, φ k • π k u ∂(muK ε)
      map_add' := fun a b => by
        simp only [map_add, smul_add]
        exact integral_add (hint a) (hint b)
      map_smul' := fun c a => by
        simp only [map_smul, RingHom.id_apply]
        simp only [smul_comm (φ _) c]
        exact integral_smul c _ }
  have hTapp : ∀ u, T u = ∫ k, φ k • π k u ∂(muK ε) := fun u => rfl
  have hTc : Continuous T := by
    refine AddMonoidHomClass.continuous_of_bound T (∫ k, ‖φ k‖ ∂(muK ε)) fun u => ?_
    calc ‖T u‖ ≤ ∫ k, ‖φ k‖ * ‖u‖ ∂(muK ε) :=
          norm_integral_le_of_norm_le ((hφc.norm.integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)).mul_const _)
            (Eventually.of_forall fun k => by rw [norm_smul, hπ.norm_apply])
      _ = (∫ k, ‖φ k‖ ∂(muK ε)) * ‖u‖ := integral_mul_const _ _
  haveI hR : FiniteDimensional ℂ (LinearMap.range T) := by
    rw [← Submodule.span_eq (LinearMap.range T), LinearMap.coe_range]
    exact hφR
  have hsurj : ∀ x : U, ∃ u ∈ D, T u = T x := by
    intro x
    haveI : FiniteDimensional ℂ (D.map T) := Submodule.finiteDimensional_of_le (LinearMap.map_le_range)
    have hcl : IsClosed ((D.map T : Submodule ℂ U) : Set U) := Submodule.closed_of_finiteDimensional _
    have hx : x ∈ closure (D : Set U) := by
      rw [← Submodule.topologicalClosure_coe, hDdense]; trivial
    have : T x ∈ closure ((D.map T : Submodule ℂ U) : Set U) := by
      rw [Submodule.map_coe]
      exact image_closure_subset_closure_image hTc ⟨x, hx, rfl⟩
    rw [hcl.closure_eq] at this
    obtain ⟨u, hu, hTu⟩ := this
    exact ⟨u, hu, hTu⟩
  obtain ⟨u, hu, hTu⟩ := hsurj s
  obtain ⟨u', hu', hTu'⟩ := hsurj s'
  rw [hTapp, hTapp, hφS s hs] at hTu
  rw [hTapp, hTapp, hφS s' hs'] at hTu'
  have hp : (1 : ℝ) ≤ 2 + e := by linarith
  have h0 := GlobalTheory.T.integrable_matrixCoeff_cyclic_span n ε μ U π hπ (2 + e) hp v (hv e he) u hu u' hu'
  have h1 := GlobalTheory.T.integrable_matrixCoeff_K_average_right n ε μ U π hπ (2 + e) hp φ hφc u u' h0
  have h2 := GlobalTheory.T.integrable_matrixCoeff_K_average_left n ε μ U π hπ (2 + e) hp φ hφc (∫ k, φ k • π k u ∂(muK ε)) u' h1
  rw [hTu, hTu'] at h2
  exact h2

end GlobalTheory.TempKFin

end
