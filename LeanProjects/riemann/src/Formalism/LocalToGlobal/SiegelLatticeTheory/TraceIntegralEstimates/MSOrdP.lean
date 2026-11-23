import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyMS
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrdFull
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValDiffProd

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S IsDedekindDomain

namespace Formalism.L2.S.Pv.MSOrdP

open Formalism.L2.SG.LocVol Formalism.L2.SG.Pf.Carrier.EnergyConst Formalism.L2.SG.Pf.Carrier.EnergyMS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem three_dvd (r : ℕ) : 3 ∣ (r + 1) * (8 * r ^ 2 + 10 * r + 3) := by
  obtain ⟨k, hk | hk | hk⟩ : ∃ k, r = 3 * k ∨ r = 3 * k + 1 ∨ r = 3 * k + 2 := ⟨r / 3, by omega⟩
  · subst hk
    exact ⟨(3 * k + 1) * (24 * k ^ 2 + 10 * k + 1), by ring⟩
  · subst hk
    exact ⟨(3 * k + 2) * (24 * k ^ 2 + 26 * k + 7), by ring⟩
  · subst hk
    exact ⟨(k + 1) * (8 * (3 * k + 2) ^ 2 + 10 * (3 * k + 2) + 3), by ring⟩

theorem dimension_exponent_real (D : D7) : ((e1 D : ℕ) : ℝ) =
    ((D.R.rS : ℝ) + 1) * (8 * (D.R.rS : ℝ) ^ 2 + 10 * D.R.rS + 3) / 3 := by
  unfold e1
  rw [Nat.cast_div (three_dvd D.R.rS) (by norm_num)]
  push_cast
  ring

theorem msOrd_holds : MSOrd := by
  intro D X u u' ψ hψ hs v hv
  have h := Formalism.L2.SG.Pf.NcVal.volOrdV_holds X u u' ψ hψ hs v hv
  rw [Formalism.L2.SG.Pf.NcVal.absV_dV] at h
  have hn0 : ((Ideal.absNorm (v.maxPowDividing (differentIdeal ℤ (𝓞 X.B.I.F))) : ℕ) : ℝ) ≠ 0 := by
    have hI : v.maxPowDividing (differentIdeal ℤ (𝓞 X.B.I.F)) ≠ ⊥ := by
      unfold HeightOneSpectrum.maxPowDividing
      exact pow_ne_zero _ v.ne_bot
    exact_mod_cast (mt Ideal.absNorm_eq_zero_iff.1 hI)
  have hc : ((Ideal.absNorm (v.maxPowDividing (differentIdeal ℤ (𝓞 X.B.I.F))) : ℕ) : ℝ)⁻¹ ^
      (-(((D.R.rS : ℝ) + 1) * (8 * (D.R.rS : ℝ) ^ 2 + 10 * D.R.rS + 3) / 3)) = dN X v ^ e1 D := by
    rw [← dimension_exponent_real D, Real.inv_rpow (Nat.cast_nonneg _), Real.rpow_neg (Nat.cast_nonneg _), inv_inv,
      Real.rpow_natCast]
    rfl
  rw [hc] at h
  have hpos : (0 : ℝ) < dN X v := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hn0)
  have hZ : ZZX X u u' ψ v ≠ 0 := by
    intro h0
    rw [h0, div_zero] at h
    have : (0 : ℝ) < dN X v ^ e1 D := pow_pos hpos _
    linarith
  rw [div_eq_iff hZ] at h
  exact h

end Formalism.L2.S.Pv.MSOrdP
