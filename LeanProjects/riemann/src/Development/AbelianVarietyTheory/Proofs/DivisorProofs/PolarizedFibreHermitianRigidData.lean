import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffTopMonEqZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HolomorphicUniformizationTangentUnimodularRiemann
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionSectionPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedFibreUniformizationModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizationLinearEquivUniqueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentCombinationVectorOverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeHeightNormFormulaStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.SecJet GlobalTheory.CovTop

namespace GlobalTheory.UnifAtPlace

theorem exists_unifData : ∀ (K : Type) [Field K] [NumberField K] (F : SemiFib K) (h : HermFam K (Fin F.P₀.g → K)) (ρ : (K →+* ℂ) → ℝ) (K'' : Type) [Field K''] [NumberField K''] [Algebra K K''] (h'' : HermFam K'' (Fin F.P₀.g → K'')) (P : Out.PolAV (Sp K'')) (ψ : P.A.left ⟶ F.P₀.A.left) (AA : Over (Sp (𝓞 K''))) [GrpObj AA] [IsCommMonObj AA] (φ : P.A.left ⟶ AA.left) (MM : RigLB AA) (N : ℕ) (w : LB.Iso (MM.L.pull φ) (lbPow P.L N)) (r : ℕ) (b : Fin r → (lbPow P.L N).Sec) (v' : Fin F.P₀.g → (epsR K'' ⟶ P.A)) (x : Fin F.P₀.g → K'') (σ : K'' →+* ℂ), 1 ≤ N → F.IsHerm h → F.IsRho ρ → IsBC h h'' → GlobalTheory.IsPolFibre (algebraMap K K'') F.P₀ P ψ → IsModel w → (∀ k, GlobalTheory.IsVecOver (algebraMap K K'') ψ (F.v k) (v' k)) → IsLieBasis v' → ∃ (Q : Out.PolAV (Sp ℂ)) (ψσ : Q.A.left ⟶ P.A.left) (wσ : LB.Iso ((lbPow P.L N).pull ψσ) (lbPow Q.L N)) (s : Fin r → (lbPow Q.L N).Sec) (u : HolUnif Q.A Q.L F.P₀.g) (Hm : Matrix (Fin F.P₀.g) (Fin F.P₀.g) ℂ) (χ : u.Λ → ℂ) (ρ' : ℂ) (θ : Fin r → (Fin F.P₀.g → ℂ) → ℂ) (Fd : Set (Fin F.P₀.g → ℂ)) (yq : epsR ℂ ⟶ Q.A) (Y0 : Fin F.P₀.g → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ), GlobalTheory.IsPolFibre σ P Q ψσ ∧ wσ.IsGen ∧ (∀ a, SecMaps wσ (secPull (b a) ψσ) (s a)) ∧ u.IsAH Hm χ ∧ RigIs w σ wσ u ρ' ∧ (∀ a, u.IsFnPow N (s a) (θ a)) ∧ (∀ a, u.IsThetaFn Hm χ N (θ a)) ∧ IsAddFundamentalDomain u.Λ Fd volume ∧ GlobalTheory.IsVecOver σ ψσ (tanComb x v') yq ∧ u.IsDiff Y0 yq ∧ h''.nrm σ x = √(Real.pi * (hermForm Hm Y0 Y0).re) ∧ IsLeast {t | ∃ z ∈ u.Λ, z ≠ 0 ∧ t = √(hermForm Hm z z).re} (ρ (σ.comp (algebraMap K K''))) ∧ (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef ∧ ρ' ≠ 0 := by
  intro K _ _ F h ρ K'' _ _ _ h'' P ψ AA _ _ φ MM N w r b v' x σ _hN hH hR hBC hP hM hv' hL
  obtain ⟨Λ, Hm, W, ⟨Q, e, ψ₁, v₁, u, χ, hQ, hΛ, hAH, hv₁⟩, hHW⟩ := hH (σ.comp (algebraMap K K''))
  obtain ⟨ψσ, hcomp, hψσ⟩ := GlobalTheory.CM.EllComp.exists_isPolFibre_lift hP hQ
  have hwσ : LBIso ((lbPow P.L N).pull ψσ) (lbPow Q.L N) :=
    LBIso.trans (pull_isLB (GlobalTheory.isLB_lbPow P.isLB N) ψσ) (GlobalTheory.isLB_lbPow (pull_isLB P.isLB ψσ) N)
      (GlobalTheory.isLB_lbPow Q.isLB N) (GlobalTheory.lbIso_lbPow_pull P.isLB ψσ N).symm (GlobalTheory.lbIso_lbPow hψσ.2.2 N)
  obtain ⟨wσ, hwσg⟩ := hwσ
  choose sa hsa using fun a => GlobalTheory.exists_secMaps (pull_isLB (GlobalTheory.isLB_lbPow P.isLB N) ψσ)
    (GlobalTheory.isLB_lbPow Q.isLB N) wσ hwσg (secPull (b a) ψσ)
  choose θ hθ₁ hθ₂ using fun a => GlobalTheory.T.theta_function_section_power Q.A Q.L _ u Hm χ Q.isLB hAH N (sa a)
  obtain ⟨ρ', hρ', hρ'0⟩ := GlobalTheory.T.polarized_fibre_uniformization_model K'' P AA φ MM N w σ Q ψσ wσ _ u hM hψσ hwσg
  obtain ⟨Fd, hFd⟩ := GlobalTheory.KeyPow.exists_isAddFundamentalDomain u
  have hvv : ∀ k, GlobalTheory.IsVecOver σ ψσ (v' k) (v₁ k) := fun k =>
    GlobalTheory.CM.EllComp.isVecOver_cancel hP.2.1.1 hψσ.2.1.1 (hv' k) (by rw [hcomp]; exact (hv₁ k).1)
  obtain ⟨hy₁, hy₂⟩ := GlobalTheory.T.tangent_combination_vector_over K'' P Q σ ψσ F.P₀.g v' v₁ x F.P₀.g u W hψσ hL.1 hvv (fun k => (hv₁ k).2)
  have hn := GlobalTheory.T.base_change_height_norm_formula K K'' F.P₀.g F.P₀.g h h'' σ Hm W x hBC hHW
  obtain ⟨Λ₂, Hm₂, W₂, ⟨Q₂, e₂, ψ₂, v₂, u₂, χ₂, hQ₂, hΛ₂, hAH₂, -⟩, hleast⟩ := hR (σ.comp (algebraMap K K''))
  obtain ⟨T, hTΛ, hTH⟩ := GlobalTheory.T.uniformization_linear_equiv_unique K (σ.comp (algebraMap K K'')) F.P₀ Q Q₂ ψ₁ ψ₂ F.P₀.g u u₂ Hm Hm₂ χ χ₂ e e₂ hQ hQ₂ hAH hAH₂
  have hset : {t | ∃ z ∈ u.Λ, z ≠ 0 ∧ t = √(hermForm Hm z z).re} =
      {t | ∃ z ∈ Λ₂, z ≠ 0 ∧ t = √(hermForm Hm₂ z z).re} := by
    ext t
    constructor
    · rintro ⟨z, hz, hz0, rfl⟩
      exact ⟨T z, hΛ₂ ▸ (hTΛ z).2 hz, fun h0 => hz0 (T.injective (h0.trans (map_zero T).symm)), by rw [hTH]⟩
    · rintro ⟨z, hz, hz0, rfl⟩
      refine ⟨T.symm z, (hTΛ _).1 (by rw [T.apply_symm_apply, hΛ₂]; exact hz), fun h0 => hz0 ?_, ?_⟩
      · rw [← T.apply_symm_apply z, h0, map_zero]
      · rw [← hTH, T.apply_symm_apply]
  have hEf : ∀ (Q : Out.PolAV (Sp ℂ)) (g : ℕ) (u : HolUnif Q.A Q.L g) (Hm : Matrix (Fin g) (Fin g) ℂ)
      (χ : u.Λ → ℂ), Q.g = g → u.IsAH Hm χ → ∃ Ef : LinearMap.BilinForm ℤ u.Λ,
        (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef := by
    intro Q g u Hm χ e hA
    cases Q
    subst e
    exact (GlobalTheory.AnyUnif.tangent_and_unimodular GlobalTheory.thetaUnifAV_all _ u).2.2 Hm χ hA
  obtain ⟨Ef, hEf₁, hEf₂⟩ := hEf Q _ u Hm χ e hAH
  exact ⟨Q, ψσ, wσ, sa, u, Hm, χ, ρ', θ, Fd, _, _, Ef, hψσ, hwσg, hsa, hAH, hρ', hθ₁, hθ₂, hFd, hy₁, hy₂, hn,
    hset ▸ hleast, hEf₁, hEf₂, hρ'0⟩

end GlobalTheory.UnifAtPlace
