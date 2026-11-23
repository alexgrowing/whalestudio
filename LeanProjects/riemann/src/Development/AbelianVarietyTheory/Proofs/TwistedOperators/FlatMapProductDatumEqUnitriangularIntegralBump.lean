import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousReprSymm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfPartOneSubEInfSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergOperatorThetaFunctionalMixedSourceMode
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergThetaMixedModelTargetOfMixedModel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionMixedCoordinateBumpMulCoreStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTargetBumpMulCoreThetaExistsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaFunctionDeterminedByMixedCoordinatesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.FlatProdValue

variable {D : D7}

theorem mixT_smul' {S T T₀ : HSp D} {ρ : ℕ} (d : HypDec T T₀ ρ) (ψ : AddChar (AF D.host.F) ℂ)
    (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank)) (c : ℂ) (f : WO S T → ℂ) (y : Mx D S.rank ρ) :
    d.mixT S ψ μ 𝓕 (c • f) y = c • d.mixT S ψ μ 𝓕 f y := by
  funext w
  simp only [HypDec.mixT, heisO, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1; funext ξ; ring

theorem continuous_psiUni' {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) (ρ : ℕ) :
    Continuous fun u : UX D ρ => psiUni ψ u.1 := by
  have : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  have hc : Continuous fun u : UX D ρ => (u.1.1 : Mx D ρ ρ) := Units.continuous_val.comp continuous_subtype_val
  have hu : Continuous fun u : UX D ρ => upSum (u.1.1 : Mx D ρ ρ) := by
    unfold upSum
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    split_ifs
    · exact (continuous_apply j).comp ((continuous_apply i).comp hc)
    · exact continuous_const
  exact hψ.comp (ht.comp hu)

theorem flatS_ne_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (β₁ : Mx D W.rank ρ → ℝ) (β₂ : Mx D V₀.rank σ → ℂ) (g : WO V₀ W₀ → ℂ) (g' : WO V₀ W → ℂ) (Φ : WO V W → ℂ), g ≠ 0 → β₂ y ≠ 0 → (∀ x', dV.mixS W ψ s.vS.μ s.vS.𝓕 Φ x' = (β₁ x' : ℂ) • g') → (∀ y', dW.mixT V₀ ψ s.vT.μ s.vT.𝓕 g' y' = β₂ y' • g) → Continuous β₁ → β₁ x = 1 → (∀ z, 0 ≤ β₁ z) → (∀ u : UX D ρ, β₁ (x ⬝ u.1.1) ≠ 0 → 0 < (star (psiUni ψ u.1)).re) → HasCompactSupport (fun u : UX D ρ => β₁ (x ⬝ u.1.1)) → flatS dV dW s x y Φ ≠ 0 := by
  intro D ψ hψ V V₀ W W₀ ρ σ dV dW s x y β₁ β₂ g g' Φ hg hβy hS hT hβc hβx hβ0 hpos hcs
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE D) := IsModuleTopology.isTopologicalRing (AF D.host.F) (AE D)
  haveI : (s.vU.ν).IsHaarMeasure := s.vU.unit.1
  obtain ⟨w, hw⟩ := Function.ne_iff.1 hg
  set F : UX D ρ → ℂ := fun u => star (psiUni ψ u.1) * (β₁ (x ⬝ u.1.1) : ℂ) with hF
  have hval : flatS dV dW s x y Φ w = (∫ u, F u ∂s.vU.ν) * (β₂ y * g w) := by
    simp only [flatS, flatAt, flatFun, evalAt, hS, mixT_smul', hT, Pi.smul_apply, smul_eq_mul, hF]
    rw [← integral_mul_const]
    congr 1; funext u; ring
  have hxc : Continuous fun u : UX D ρ => x ⬝ u.1.1 :=
    continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)
  have hβc' : Continuous fun u : UX D ρ => β₁ (x ⬝ u.1.1) := hβc.comp hxc
  have hFc : Continuous F :=
    (continuous_star.comp (continuous_psiUni' hψ.1.1 ρ)).mul (Complex.continuous_ofReal.comp hβc')
  have hFs : HasCompactSupport F := by
    have : HasCompactSupport fun u : UX D ρ => (β₁ (x ⬝ u.1.1) : ℂ) := hcs.comp_left Complex.ofReal_zero
    exact this.mul_left
  have hFi : Integrable F s.vU.ν := hFc.integrable_of_hasCompactSupport hFs
  have hre : ∀ u, (F u).re = (star (psiUni ψ u.1)).re * β₁ (x ⬝ u.1.1) := by
    intro u; simp [hF, Complex.mul_re]
  have hpos' : 0 < ∫ u, (F u).re ∂s.vU.ν := by
    have hrc : Continuous fun u => (F u).re := Complex.continuous_re.comp hFc
    have hrs : HasCompactSupport fun u => (F u).re := hFs.comp_left Complex.zero_re
    refine hrc.integral_pos_of_hasCompactSupport_nonneg_nonzero hrs (x := 1) ?_ ?_
    · intro u
      simp only [Pi.zero_apply, hre]
      by_cases h0 : β₁ (x ⬝ u.1.1) = 0
      · rw [h0, mul_zero]
      · exact mul_nonneg (hpos u h0).le (hβ0 _)
    · have h1 : x ⬝ ((1 : UX D ρ).1.1) = x := by simp
      rw [hre, h1, hβx, mul_one]
      have := hpos 1 (by rw [h1, hβx]; exact one_ne_zero)
      exact this.ne'
  have hI : (∫ u, F u ∂s.vU.ν) ≠ 0 := by
    intro h0
    have e : ∫ u, (F u).re ∂s.vU.ν = (∫ u, F u ∂s.vU.ν).re := integral_re hFi
    rw [h0, Complex.zero_re] at e
    linarith
  intro h0
  have := congrFun h0 w
  rw [hval, Pi.zero_apply] at this
  exact mul_ne_zero hI (mul_ne_zero hβy hw) this

end GlobalTheory.FlatProdValue

end
