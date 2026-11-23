import Development.AutomorphicArithmetic.TwistedTraces.CasimirEqOfOrthonormalBases
import Development.AutomorphicArithmetic.TwistedTraces.ExistsSignedBasisLieSubalgebraExpCompact
import Development.AutomorphicArithmetic.TwistedTraces.NormCuspVecLGkActionLeOfAevalEqZero
import Development.AutomorphicArithmetic.TwistedTraces.NormApplyLeOfLaplacianLowerBound
import Development.AutomorphicArithmetic.TwistedTraces.ReInnerGeOfSpanEigenvectors
import Development.AutomorphicArithmetic.TwistedTraces.FiniteDimensionalCuspFormsOfLevelAndDerivOpBound
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.ConvolutionTheory.C.nearFinite :
    UpperTheory.ConvolutionTheory.C.NearFinite := by
  intro K _ _ n ι _ _ b ε hε horth U hU X _ _ _ τ c
  obtain ⟨B, hB, hsym, d, b', ε', hε', horth', hK⟩ := UpperTheory.exists_signed_basis_lieSubalgebra_exp_compact K n
  have hcas : casimir b ε = casimir b' ε' :=
    UpperTheory.casimir_eq_of_orthonormal_bases _ B ι (Fin d) b ε b' ε' hsym hε (fun i j => by rw [hB, horth])
      (fun i => by rcases hε' i with h | h <;> rw [h] <;> norm_num) horth'
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure (normOneGL K n), μ.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  have hM : ∀ i, ∃ M : ℝ, ε' i = -1 → ∀ φ ∈ centralCuspForms K n,
      (∀ k, Polynomial.aeval ((gkModuleCusp K n).σ k) (LinearMap.charpoly (τ k)) φ = 0) →
      ‖cuspVecL μ ((gkModuleCusp K n).ρ (b' i) φ)‖ ≤ M * ‖cuspVecL μ φ‖ := by
    intro i
    by_cases hi : ε' i = -1
    · obtain ⟨M, hM⟩ := UpperTheory.norm_cuspVecL_gk_action_le_of_aeval_eq_zero K n μ (Module.finrank ℂ X) (fun k => LinearMap.charpoly (τ k)) (b' i)
        (fun k => ⟨(LinearMap.charpoly_monic _).ne_zero, (LinearMap.charpoly_natDegree _).le⟩) (hK i hi)
      exact ⟨M, fun _ => hM⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose M hM using hM
  obtain ⟨C', hC'⟩ := UpperTheory.norm_apply_le_of_laplacian_lower_bound d c (∑ i, |M i|) ε' hε'
  rw [hcas]
  suffices key : ∀ s : Set (cuspForms K n), (∀ φ ∈ s, φ ∈ centralCuspForms K n ∧
      (∀ u ∈ U, ∀ g, φ.1 (g * finEmb K n (u : AdelicGLn.integralFiniteGL K n)) = φ.1 g) ∧
      (∃ f : X →ₗ[ℂ] cuspForms K n, (∀ k x g, (f (τ k x)).1 g = (f x).1 (g * infEmb K n (k : archGroup K n))) ∧
        φ ∈ LinearMap.range f) ∧
      ∃ (h : φ.1 ∈ archSmooth K n) (κ : ℂ), -c ≤ κ.re ∧
        uAction (casimir b' ε') ⟨φ.1, h⟩ = κ • ⟨φ.1, h⟩) → FiniteDimensional ℂ (Submodule.span ℂ s) from
    key _ fun _ h => h
  intro s hs
  have hcent : Submodule.span ℂ s ≤ centralCuspForms K n := Submodule.span_le.2 fun φ hφ => (hs φ hφ).1
  have hskew : ∀ Y, ∀ x ∈ centralCuspForms K n, ∀ y ∈ centralCuspForms K n,
      inner ℂ (cuspVecL μ ((gkModuleCusp K n).ρ Y x)) (cuspVecL μ y) +
        inner ℂ (cuspVecL μ x) (cuspVecL μ ((gkModuleCusp K n).ρ Y y)) = 0 :=
    fun Y x hx y hy => petersson_inner_lieAlgebra_skewAdjoint μ Y hx hy
  have hT : ∀ φ : cuspForms K n, uActionCusp K n (casimir b' ε') φ =
      ∑ i, (ε' i : ℂ) • (gkModuleCusp K n).ρ (b' i) ((gkModuleCusp K n).ρ (b' i) φ) := by
    intro φ
    simp only [casimir, map_sum, map_smul, map_mul, LinearMap.sum_apply, LinearMap.smul_apply,
      Module.End.mul_apply, gkModuleCusp_ρ_apply, Complex.coe_smul]
  have hsymT : ∀ x ∈ centralCuspForms K n, ∀ y ∈ centralCuspForms K n,
      inner ℂ (cuspVecL μ (uActionCusp K n (casimir b' ε') x)) (cuspVecL μ y) =
        inner ℂ (cuspVecL μ x) (cuspVecL μ (uActionCusp K n (casimir b' ε') y)) := by
    intro x hx y hy
    rw [hT, hT, map_sum, map_sum, sum_inner, inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := hskew (b' i) _ (ρ_mem_centralCuspForms (b' i) hx) y hy
    have h2 := hskew (b' i) x hx _ (ρ_mem_centralCuspForms (b' i) hy)
    rw [map_smul, map_smul, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    linear_combination (ε' i : ℂ) * (h1 - h2)
  have hlow := UpperTheory.re_inner_ge_of_span_eigenvectors _ _ (cuspVecL μ) (centralCuspForms K n) (uActionCusp K n (casimir b' ε')) c s hsymT
    (fun x hx => by
      obtain ⟨h1, -, -, h, κ, hκ, he⟩ := hs x hx
      exact ⟨h1, κ, hκ, Subtype.ext (congrArg (fun ψ : archSmooth K n => (ψ : AdelicGLn.AdelicGL K n → ℂ)) he)⟩)
  have hpoly : ∀ k, ∀ φ ∈ Submodule.span ℂ s,
      Polynomial.aeval ((gkModuleCusp K n).σ k) (LinearMap.charpoly (τ k)) φ = 0 := by
    intro k
    have hle : Submodule.span ℂ s ≤
        LinearMap.ker (Polynomial.aeval ((gkModuleCusp K n).σ k) (LinearMap.charpoly (τ k))) := by
      refine Submodule.span_le.2 ?_
      intro φ hφ
      obtain ⟨-, -, ⟨f, hf, x, rfl⟩, -⟩ := hs φ hφ
      have h := map_aeval_apply_of_intertwine f (A := τ k) (B := (gkModuleCusp K n).σ k)
        (fun m => Subtype.ext (funext fun g => hf k m g)) (LinearMap.charpoly (τ k)) x
      rw [LinearMap.aeval_self_charpoly, LinearMap.zero_apply, map_zero] at h
      exact h.symm
    exact fun φ hφ => hle hφ
  refine UpperTheory.finiteDimensional_cuspForms_of_level_and_derivOp_bound K n μ d b' C' U _ hU hcent (fun φ hφ u hu => ?_) (fun φ hφ => ?_)
  · have hle : Submodule.span ℂ s ≤ LinearMap.eqLocus
        (finRepCusp K n (u : AdelicGLn.integralFiniteGL K n)) LinearMap.id :=
      Submodule.span_le.2 fun ψ hψ => Subtype.ext (funext fun g => (hs ψ hψ).2.1 u hu g)
    exact hle hφ
  · refine hC' _ _ (cuspVecL μ) (centralCuspForms K n) (fun i => (gkModuleCusp K n).ρ (b' i))
      (fun i x hx => ρ_mem_centralCuspForms _ hx) (fun i => hskew (b' i)) φ (hcent hφ) ?_ fun i hi => ?_
    · rw [← hT]
      exact hlow φ hφ
    · refine (hM i hi φ (hcent hφ) fun k => hpoly k φ hφ).trans ?_
      refine mul_le_mul_of_nonneg_right ((le_abs_self _).trans ?_) (norm_nonneg _)
      exact Finset.single_le_sum (f := fun i => |M i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
