import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
import Development.AutomorphicArithmetic.TwistedTraces.ExistsNhdsDisplacementLeHalfOfDerivOpBound
import Development.AutomorphicArithmetic.TwistedTraces.ExistsNhdsOneNormOneGLFactorization
import Development.AutomorphicArithmetic.TwistedTraces.ExistsApproximateIdentityIntegrated
import Development.AutomorphicArithmetic.TwistedTraces.FiniteDimensionalOfCompactNearIdentity
import GroundTheory.AutomorphicForms.UnitaryAdmissible.CuspFinite

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.finiteDimensional_cuspForms_of_level_and_derivOp_bound :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL K n)) [μ.IsHaarMeasure] (d : ℕ) (b : Module.Basis (Fin d) ℝ (isExpLieAlgebra K n).lieSubalgebra) (C : ℝ) (U : Subgroup (AdelicGLn.integralFiniteGL K n)) (S : Submodule ℂ (cuspForms K n)), IsOpen (U : Set (AdelicGLn.integralFiniteGL K n)) → S ≤ centralCuspForms K n → (∀ φ ∈ S, ∀ u ∈ U, finRepCusp K n (u : AdelicGLn.integralFiniteGL K n) φ = φ) → (∀ φ ∈ S, ∀ i, ‖cuspVecL μ ((gkModuleCusp K n).ρ (b i) φ)‖ ≤ C * ‖cuspVecL μ φ‖) → FiniteDimensional ℂ S := by
  intro K _ _ n μ _ d b C U S hU hS hfix hbound
  obtain ⟨N, hN, hNv⟩ := UpperTheory.exists_nhds_displacement_le_half_of_derivOp_bound _ _ _ (isExpLieAlgebra K n) d b C
  obtain ⟨N', hN', hN'd⟩ := UpperTheory.exists_nhds_one_normOneGL_factorization K n N U hN hU
  obtain ⟨f, hf⟩ := UpperTheory.exists_approximate_identity_integrated (normOneGL K n) (CuspL2 μ) (cuspRepT μ) μ N' hN'
  have key : ∀ v ∈ S.map (cuspVecL μ),
      ‖(cuspRepT μ).integrated μ (UnitaryRep.ccToL1 μ f) v - v‖ ≤ 1 / 2 * ‖v‖ := by
    rintro _ ⟨φ, hφ, rfl⟩
    refine hf _ _ fun g hg => ?_
    obtain ⟨a, ha, u, hu, rfl⟩ := hN'd g hg
    have hφ' : φ ∈ centralCuspForms K n := hS hφ
    have hfx : cuspRepT μ (retractOne (finEmb K n (u : AdelicGLn.integralFiniteGL K n))) (cuspVecL μ φ) =
        cuspVecL μ φ := by
      rw [← cuspToL2_finRepCusp μ _ hφ', hfix φ hφ u hu]
    rw [(cuspRepT μ).map_mul_apply, hfx, ← archRepT_apply]
    refine hNv (CuspL2 μ) (archRepT μ) (cuspVecL μ φ) (fun g w => ?_)
      (isSmoothVector_cuspToL2 μ hφ') (fun i => ?_) a ha
    · rw [archRepT_apply]
      exact UnitaryRep.norm_map _ _ _
    · rw [derivOp_cuspVecL μ hφ']
      exact hbound φ hφ i
  haveI : FiniteDimensional ℂ (S.map (cuspVecL μ)) :=
    UpperTheory.finiteDimensional_of_compact_near_identity (CuspL2 μ) _ (S.map (cuspVecL μ)) (isCompactOperator_cuspRep μ f) key
  exact UnitaryAdmissible.finiteDimensional_of_map_mem (E := S.map (cuspVecL μ)) (cuspVecL μ)
    (fun x hx => Submodule.mem_map_of_mem hx)
    (fun x hx h => eq_zero_of_cuspVecL_eq_zero (μ := μ) (hS hx) h)
