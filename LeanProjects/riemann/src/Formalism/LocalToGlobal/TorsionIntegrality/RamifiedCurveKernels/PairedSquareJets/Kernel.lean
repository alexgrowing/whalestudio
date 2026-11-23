import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.StatementK
import Formalism.GaussJetBounds.FinalB
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Hurwitz
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.HurwitzB
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.FirstLevelFromUniversalLaw
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveSecondLogDerivative

noncomputable section
open scoped BigOperators

namespace Formalism.L2.Th1.G

open Formalism.L2.Th1.C
open Formalism.L2.Th1.A (logSer expSer wpReg)
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPair jetPairPoly minorProd)

namespace TwoKernelNormBounds

theorem constantCoeff_betaPair {K : Type} [Field K] (H : Type) [Fintype H] (N0 N1 : ℕ) (u : H → K) :
    MvPowerSeries.constantCoeff (betaPair H N0 N1 u) = 0 := by
  simp [betaPair]

theorem norm_mul_le_one_of_half {K : Type} [NormedField K] (S th : K) (r : ℝ) (hr : 0 < r)
    (hS : ‖S‖ ≤ r ^ (-(1 / 2 : ℝ))) (hth : ‖th‖ ≤ r ^ (1 / 2 : ℝ)) : ‖S * th‖ ≤ 1 := by
  rw [norm_mul]
  calc ‖S‖ * ‖th‖ ≤ r ^ (-(1 / 2 : ℝ)) * r ^ (1 / 2 : ℝ) :=
        mul_le_mul hS hth (norm_nonneg _) (Real.rpow_nonneg hr.le _)
    _ = 1 := by rw [← Real.rpow_add hr]; norm_num

theorem hasSubst_lin {K : Type} [Field K] {n m : Type} [Fintype n] [Fintype m] (A : n → m → K) :
    MvPowerSeries.HasSubst
      (fun i => (∑ x, MvPowerSeries.C (A i x) * MvPowerSeries.X x : MvPowerSeries m K)) := by
  first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by simp)
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun i => by simp [IsNilpotent.zero])
    | exact ⟨fun i => by simp [IsNilpotent.zero], by simp [Filter.cofinite_eq_bot]⟩

theorem linSub_sqSum {K : Type} [Field K] {n m : Type} [Fintype n] [Fintype m] (A : n → m → K)
    (c : n → K) :
    linSub A (sqSum c) =
      ∑ i, MvPowerSeries.C (c i) * (∑ x, MvPowerSeries.C (A i x) * MvPowerSeries.X x) ^ 2 := by
  have ha := hasSubst_lin A
  unfold linSub sqSum
  rw [← MvPowerSeries.coe_substAlgHom ha, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_mul, map_pow, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X ha]
  congr 1
  have h := (MvPowerSeries.substAlgHom ha).commutes (c i)
  simpa [MvPowerSeries.coe_substAlgHom, MvPowerSeries.algebraMap_apply] using h

end TwoKernelNormBounds

open TwoKernelNormBounds

theorem KernelShape_of (hO : ShapeOrth) (hC : ShapeCong) : KernelShape := by
  intro K _ _ _ l linv ph d hlp hu hph hSh hd H _ N0 N1 n _ c A u th Q2 h2 hc hA hth hQ0 hQ hlin G hG
  obtain ⟨J, hJ, hJe⟩ := hO K l linv ph d hlp hu hph hSh n c hc G hG
  have hdpos : 0 < ‖(d : K)‖ := norm_pos_iff.mpr hd
  obtain ⟨sg, hsg, hsge⟩ := hC K n _ (jet l ph 2) th c A (betaPair H N0 N1 u) Q2 h2
    (norm_mul_le_one_of_half _ _ _ hdpos hSh.1 hth) hA (constantCoeff_betaPair H N0 N1 u) hQ0 hQ hlin
    J hJ
  refine ⟨sg, hsg, ?_⟩
  unfold kernelAt
  rw [hJe, hsge]
  rfl

theorem KernelThmB_of (hS : KernelShape) : KernelThmB := by
  intro K _ _ _ l linv ph d hlp hu hph hSh hd0 hd1 H _ _ N0 N1 n _ c A u th Q2 h2 hc hA hth hu1 hQ0 hQ
    hlin G hG x hx hdet TT colN p hp hp1 I nu1 nu2 size h1 h2' h3
  obtain ⟨sg, hsg, he⟩ := hS K l linv ph d hlp hu hph hSh (norm_pos_iff.mp hd0) H N0 N1 n c A u th Q2
    h2 hc hA hth hQ0 hQ hlin G hG
  rw [he]
  exact Formalism.DworkPowerSeriesWeights.thmB K ‖(d : K)‖ hd0 hd1 H N0 N1 (jet l ph 2) u hSh.1 hu1 sg hsg x hx hdet TT colN p
    hp hp1 I nu1 nu2 size h1 h2' h3

theorem KernelThmBGauss_of (hS : KernelShape) : KernelThmBGauss := by
  intro p _ l linv ph hlp hu hph hSh H _ _ N0 N1 n _ c A u th Q2 h2 hc hA hth hu1 hQ0 hQ
    hlin G hG TT colN ht hht hht1 I nu1 nu2 size h1 h2' h3 nn
  have hp0 : ((p : ℕ) : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  obtain ⟨sg, hsg, he⟩ := hS ℂ_[p] l linv ph p hlp hu hph hSh hp0 H N0 N1 n c A u th Q2
    h2 hc hA hth hQ0 hQ hlin G hG
  rw [he]
  exact Formalism.DworkPowerSeriesWeights.thmBGauss p H N0 N1 (jet l ph 2) u hSh.1 hu1 sg hsg TT colN ht hht hht1 I nu1 nu2
    size h1 h2' h3 nn

end Formalism.L2.Th1.G
