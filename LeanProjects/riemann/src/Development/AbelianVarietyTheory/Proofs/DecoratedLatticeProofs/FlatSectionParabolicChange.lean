import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemDoublingSiegelParabolicIffChartMemSiegelUnn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardUnitaryChartSiegelLeviDetEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousStandardUnitaryChartAndSymmStatement
open scoped NNReal Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem degPS_chart_isSection : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ (a : GL (Fin A.rank) (AE D)) (p : siegel A), IsConj A a κ p → ∀ (χ : (AE D)ˣ →* Circle) (s₁ : ℂ), ∀ φ ∈ degPS A a χ s₁, IsSection χ s₁ (fun x => φ (κ.symm x * (p : GA D (dblSp A))⁻¹)) ∧ ∀ (s : ℂ) (g : GA D (dblSp A)), flat A a φ s₁ s g = npow (absA D (aP A p)) (s₁ - s) * stdSec (hgtStd A a κ p) (fun x => φ (κ.symm x * (p : GA D (dblSp A))⁻¹)) s₁ s (κ (g * p)) := by
  intro D A μ hμ κ hκ a p hp χ s₁ φ hφ
  obtain ⟨hlaw, hcont, hK⟩ := (mem_degPS A a).1 hφ
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro q hq a' ha' g
    have hs : κ.symm q ∈ siegel A := (mem_siegel_iff_chart_mem_P D A μ hμ κ hκ _).2 (by simpa using hq)
    have hdet := chart_aP_eq_det D A μ hμ κ hκ ⟨_, hs⟩ a' (by simpa using ha')
    have h1 := hlaw ⟨_, hs⟩ (κ.symm g * (p : GA D (dblSp A))⁻¹)
    rw [hdet] at h1
    show φ (κ.symm (q * g) * (p : GA D (dblSp A))⁻¹) = _
    rw [map_mul, mul_assoc]
    exact h1
  · exact hcont.comp (((GlobalTheory.T.continuous_standardUnitaryChart_and_symm D A μ hμ κ hκ).2).mul continuous_const)
  · obtain ⟨W, hW, hWk⟩ := isKFinite_iff.1 hK
    refine isKFinite_iff.2 ⟨W.map (LinearMap.funLeft ℂ ℂ (fun x => κ.symm x * (p : GA D (dblSp A))⁻¹)),
      inferInstance, fun k hk => ⟨_, hWk ((p : GA D (dblSp A)) * κ.symm k * (p : GA D (dblSp A))⁻¹) ?_, funext fun x => ?_⟩⟩
    · rw [hp]
      simpa [mul_assoc] using hk
    · change φ ((κ.symm x * (p : GA D (dblSp A))⁻¹) * ((p : GA D (dblSp A)) * κ.symm k * (p : GA D (dblSp A))⁻¹)) =
        φ (κ.symm (x * k) * (p : GA D (dblSp A))⁻¹)
      simp [mul_assoc]
  · intro s g
    have hr : 0 < absA D (aP A p) := hom_pos _ _
    have e1 : npow (absA D (aP A p)) (s₁ - s) * npow (absA D (aP A p)) (s - s₁) = 1 := by
      rw [← npow_add hr]; simp
    simp only [stdSec, hgtStd, map_mul, MulEquiv.symm_apply_apply, mul_inv_cancel_right, Doubling.npow_mul]
    show φ g * npow (hgt A a g) (s - s₁) = _
    linear_combination (-(φ g * npow (hgt A a g) (s - s₁))) * e1

end GlobalTheory.StdUnn
