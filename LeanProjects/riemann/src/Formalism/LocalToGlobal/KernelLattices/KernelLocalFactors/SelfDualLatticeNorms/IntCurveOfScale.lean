import Formalism.LocalToGlobal.KernelLattices.KerStd
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.BaseEx
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Formalism.LocalToGlobal.GlobalTheory.GL3.NormNatCoprime
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.ConjCls
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.ExistsPeriodPairOfIsLat
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.NormTwelveCubedEqOneOfFiveLePrime
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CubeThreeR
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral

noncomputable section
open scoped BigOperators
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker.KS

open Formalism.MainNotions Formalism.L2.Col
open Formalism.L2.Th1.E (IntCurve curveL)

theorem intCurve_of_scale (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) (L : PeriodPair) (c : ℂ) (hc : c ≠ 0)
    (h : IntCurve (curveL p (Formalism.L2.Th1.F.scalePair L c hc) ι)) (hΔ : ‖ι (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)‖ = 1) :
    IntCurve (curveL p L ι) := by
  have hH := Formalism.L2.Th1.F.homogeneity L c hc
  have h2 : (Formalism.L2.Th1.F.scalePair L c hc).g₂ = (c ^ 4)⁻¹ * L.g₂ := hH.2.2.2.2.2.2.2.2.2.1
  have h3 : (Formalism.L2.Th1.F.scalePair L c hc).g₃ = (c ^ 6)⁻¹ * L.g₃ := hH.2.2.2.2.2.2.2.2.2.2
  obtain ⟨-, -, -, h4, h6, hD⟩ := h
  have hS := fun g2 g3 : ℂ_[p] => (Formalism.L2.Th1.A.shortInv ℂ_[p] g2 g3).2.2.2
  have hιc : ι c ≠ 0 := by simpa using hc
  have hcn : ‖ι c‖ = 1 := by
    unfold curveL at hD
    rw [hS, h2, h3] at hD
    have e : ι ((c ^ 4)⁻¹ * L.g₂) ^ 3 - 27 * ι ((c ^ 6)⁻¹ * L.g₃) ^ 2 = (ι c ^ 12)⁻¹ * ι (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
      simp only [map_mul, map_inv₀, map_pow, map_sub, map_ofNat]
      field_simp
    rw [e, norm_mul, hΔ, mul_one, norm_inv, norm_pow, inv_eq_one] at hD
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 hD
  refine ⟨by simp [curveL, Formalism.L2.Th1.A.shortW], by simp [curveL, Formalism.L2.Th1.A.shortW], by simp [curveL, Formalism.L2.Th1.A.shortW], ?_, ?_, ?_⟩
  · have e : (curveL p L ι).a₄ = ι c ^ 4 * (curveL p (Formalism.L2.Th1.F.scalePair L c hc) ι).a₄ := by
      simp only [curveL, Formalism.L2.Th1.A.shortW, h2, map_mul, map_inv₀, map_pow]
      field_simp
    rw [e, norm_mul, norm_pow, hcn, one_pow, one_mul]
    exact h4
  · have e : (curveL p L ι).a₆ = ι c ^ 6 * (curveL p (Formalism.L2.Th1.F.scalePair L c hc) ι).a₆ := by
      simp only [curveL, Formalism.L2.Th1.A.shortW, h3, map_mul, map_inv₀, map_pow]
      field_simp
    rw [e, norm_mul, norm_pow, hcn, one_pow, one_mul]
    exact h6
  · unfold curveL
    rw [hS]
    simpa only [map_sub, map_mul, map_pow, map_ofNat] using hΔ

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

theorem disc_one (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : B.L.g₂ ^ 3 - 27 * B.L.g₃ ^ 2 = 1 := by
  have hL : (B.L.lattice : Set ℂ) = TaylorLogMetric.lamOf D cc δ := by
    rw [← B.lat]; rfl
  obtain ⟨e2, e3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair (TaylorLogMetric.lamOf D cc δ) B.L hL
  have h := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ
  rw [← e2, ← e3]
  exact h

theorem intCurve_base (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (ι : ℂ ≃+* ℂ_[p]) :
    IntCurve (curveL p B.L ι) := by
  have hcm : Formalism.L2.Th1.CM.HasCMBy D.host.d B.L := by
    intro ω hω
    have := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.hst B ω hω
    rwa [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.theta_val] at this
  have hd8 : D.host.d % 8 = 7 := dMod8 D
  obtain ⟨c, hc, hI⟩ := Formalism.L2.Th1.Top.good_model_exists_all_primes D.host.d B.L D.host.hyp.2.1.squarefree (by omega) hcm p hp ι
  refine intCurve_of_scale p ι B.L c hc hI ?_
  rw [disc_one B hcc hδ, map_one, norm_one]

theorem chiFac_unit (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) {N N' : ℕ}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hA : TaylorLogMetric.admitted D N N' L L') (h1 : TaylorLogMetric.EqAt D p (StandardLatticesGL3.stdL D N) L) (h2 : TaylorLogMetric.EqAt D p (StandardLatticesGL3.stdL D N') L') :
    ‖ι (Base.chiFac χ N N' L L')‖ = 1 := by
  obtain ⟨hq, hn⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC.chiFacUnit χ hχ p ((ι : ℂ →+* ℂ_[p]).comp (algebraMap TaylorLogMetric.Qbar ℂ)) N N' L L' hA h1 h2
  unfold TaylorLogMetric.lamC at hn
  rw [dif_pos hq] at hn
  exact hn

end Formalism.L2.Ker.KS
