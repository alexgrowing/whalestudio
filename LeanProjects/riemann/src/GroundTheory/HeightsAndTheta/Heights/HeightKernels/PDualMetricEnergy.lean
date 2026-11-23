import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualEnergy
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualEnergyCharts
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartEnergy
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsChartMass
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsGrassGeomDegChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo NumberField Matrix
open scoped ComplexOrder

namespace DualMetricEnergyAlt

theorem log_det_re_sub {m : Type} [Fintype m] [DecidableEq m] {H A : Matrix m m ℂ} (hH : H.PosDef)
    (hA : Function.Bijective A.mulVec) :
    Real.log (Aᴴ * H * A).det.re - Real.log (Aᴴ * A).det.re = Real.log H.det.re := by
  have hd : A.det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det A).mp (Matrix.mulVec_injective_iff_isUnit.mp hA.1)).ne_zero
  obtain ⟨hre, him⟩ := Complex.lt_def.mp hH.det_pos
  simp only [Complex.zero_re, Complex.zero_im] at hre him
  have hHd : H.det = (H.det.re : ℂ) := Complex.ext (by simp) (by simp [← him])
  have hn : 0 < Complex.normSq A.det := Complex.normSq_pos.mpr hd
  have e1 : (Aᴴ * H * A).det.re = Complex.normSq A.det * H.det.re := by
    rw [det_mul, det_mul, det_conjTranspose, hHd, mul_right_comm, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.ofReal_re]
  have e2 : (Aᴴ * A).det.re = Complex.normSq A.det := by
    rw [det_mul, det_conjTranspose, Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  rw [e1, e2, Real.log_mul hn.ne' hre.ne']
  ring

end DualMetricEnergyAlt

theorem DualMetricEnergy.proof (hD : DualEnergyCharts.Statement) (hC : ChartEnergy.Statement)
    (hG : GrassGeomDegChart.Statement) (hM : ChartMassInvariant.Statement) :
    DualMetricEnergy.Statement := by
  intro K _ _ i F T _ _ b hb hi
  obtain ⟨A, hA, hE⟩ := hD K i F T b hb hi
  obtain ⟨B, hB, hG'⟩ := hG (i - 1)
  have e1 : 1 * 1 * (i - 1) = i - 1 := by simp
  rw [e1, hG', hM _ _ (Matrix.PosDef.conjTranspose_mul_self B hB.1),
    Finset.sum_congr rfl fun k _ => hE k, Finset.sum_comm]
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  have hterm : ∀ σ : K →+* ℂ,
      ∑ k ∈ Finset.range (n + 1), chartMixedEnergy ((A σ)ᴴ * F.metric σ * A σ) ((A σ)ᴴ * A σ) k =
        1 / 2 * Real.log (F.metric σ).det.re *
          chartMass (1 : Matrix (Fin (n + 1 - 1 + 1)) (Fin (n + 1 - 1 + 1)) ℂ) := by
    intro σ
    have h := hC (n + 1 - 1) _ _ ((F.posDef σ).conjTranspose_mul_mul_same (hA σ).1)
      (Matrix.PosDef.conjTranspose_mul_self (A σ) (hA σ).1)
    have hl := DualMetricEnergyAlt.log_det_re_sub (m := Fin (n + 1)) (F.posDef σ) (hA σ)
    rw [hl] at h
    exact h
  rw [Finset.sum_congr rfl fun σ _ => hterm σ, ← Finset.sum_mul, ← Finset.mul_sum]

end GroundTheory.Heights₂.Heights
