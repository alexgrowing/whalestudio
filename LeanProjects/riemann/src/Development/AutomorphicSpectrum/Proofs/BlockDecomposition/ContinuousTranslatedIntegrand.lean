import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSummableMajorantLatticeSumStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSetIntegralOfContinuousUncurry
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.EpsteinThetaC

variable {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem continuous_scalC : Continuous (scalC : IdeleGroup k → GL ι 𝔸[k]) := by
  have hinv : Continuous fun a : IdeleGroup k ↦ ((a⁻¹ : IdeleGroup k) : 𝔸[k]) :=
    Units.continuous_val.comp continuous_inv
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j ↦ ?_
    by_cases hij : i = j
    · subst hij
      simpa [Function.comp_def, scalC, Matrix.scalar_apply] using
        (Units.continuous_val : Continuous fun a : IdeleGroup k ↦ (a : 𝔸[k]))
    · simpa [Function.comp_def, scalC, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]
        using continuous_const
  · refine continuous_matrix fun i j ↦ ?_
    by_cases hij : i = j
    · subst hij
      simpa [Function.comp_def, scalC, Matrix.scalar_apply] using hinv
    · simpa [Function.comp_def, scalC, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]
        using continuous_const

theorem thetaC_ltr (A h : GL ι 𝔸[k]) (F : (ι → 𝔸[k]) → ℂ) :
    thetaC (ltr A F) h = thetaC F (A * h) := by
  simp only [thetaC, ltr, Units.val_mul, Matrix.mulVec_mulVec]

theorem continuous_thetaC {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi k ι) :
    Continuous (thetaC F : GL ι 𝔸[k] → ℂ) := by
  refine continuous_iff_continuousAt.2 fun h₀ ↦ ?_
  obtain ⟨C, hC, hh₀⟩ := exists_compact_mem_nhds h₀
  obtain ⟨u, hu, hFu⟩ := GlobalTheory.T.exists_summable_majorant_lattice_sum hF hC
  have hcont : ContinuousOn (thetaC F : GL ι 𝔸[k] → ℂ) C := by
    refine continuousOn_tsum (fun ξ ↦ Continuous.continuousOn ?_) hu fun ξ h hh ↦ hFu h hh ξ
    refine (continuous_of_mem_schwartzBruhatPi hF).comp ?_
    exact Units.continuous_val.matrix_mulVec continuous_const
  exact hcont.continuousAt hh₀

noncomputable def translatedIntegrand (w : InfinitePlace k) (Ψ : (ι → 𝔸[k]) → ℂ)
    (ω : HeckeCharacter k) (p : {r : ℝ // 0 < r} × GL ι 𝔸[k]) (u : normOneSubgroup k) : ℂ :=
  thetaC Ψ (p.2 * scalC (moduleSection w p.1 * (u : IdeleGroup k))) *
    (ω.toIdele (u : IdeleGroup k) : ℂ)

theorem continuous_translatedIntegrand (w : InfinitePlace k) {Ψ : (ι → 𝔸[k]) → ℂ}
    (hΨ : Ψ ∈ schwartzBruhatPi k ι) (ω : HeckeCharacter k) :
    Continuous (Function.uncurry (translatedIntegrand w Ψ ω)) := by
  have hu : Continuous fun x : ({r : ℝ // 0 < r} × GL ι 𝔸[k]) × normOneSubgroup k ↦
      (x.2 : IdeleGroup k) := continuous_subtype_val.comp continuous_snd
  have hs : Continuous fun x : ({r : ℝ // 0 < r} × GL ι 𝔸[k]) × normOneSubgroup k ↦
      moduleSection w x.1.1 :=
    (continuous_moduleSection w).comp (continuous_fst.comp continuous_fst)
  have hg : Continuous fun x : ({r : ℝ // 0 < r} × GL ι 𝔸[k]) × normOneSubgroup k ↦
      x.1.2 := continuous_snd.comp continuous_fst
  exact ((continuous_thetaC hΨ).comp (hg.mul (continuous_scalC.comp (hs.mul hu)))).mul
    (continuous_subtype_val.comp (ω.continuous_toIdele.comp hu))

theorem continuous_thetaCInt_ltr {k : Type} [Field k] [NumberField k] {ι : Type} [Fintype ι]
    [DecidableEq ι] (w : InfinitePlace k) {Ψ : (ι → 𝔸[k]) → ℂ}
    (hΨ : Ψ ∈ schwartzBruhatPi k ι) (ω : HeckeCharacter k) :
    Continuous fun p : {r : ℝ // 0 < r} × GL ι 𝔸[k] ↦ thetaCInt w (ltr p.2 Ψ) ω p.1 := by
  have h := GlobalTheory.CompanionTheory.EisRk1Theta.continuous_setIntegral_of_continuous_uncurry (normOneMeasure k)
    (isCompact_closure_normOneFundamentalDomain k)
    (normOneMeasure_normOneFundamentalDomain_lt_top k) (continuous_translatedIntegrand w hΨ ω)
  refine h.congr fun p ↦ ?_
  simp only [thetaCInt, thetaC_ltr, translatedIntegrand]

end GlobalTheory.CompanionTheory.EpsteinThetaC
