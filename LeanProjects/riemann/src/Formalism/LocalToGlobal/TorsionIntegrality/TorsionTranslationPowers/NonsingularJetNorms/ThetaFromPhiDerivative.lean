import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Joints
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.ShiftAnalyticW
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Series

open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

namespace Two

variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]

theorem fExp_zero : Formalism.L2.Th1.B.fExp (0 : PowerSeries K) = 1 := by
  have h := Formalism.L2.Th1.B.fExp_add (K := K) (ι := Unit) (f := 0) (g := 0) (map_zero _) (map_zero _)
  rw [add_zero] at h
  have hc : MvPowerSeries.constantCoeff (Formalism.L2.Th1.B.fExp (0 : MvPowerSeries Unit K)) = 1 :=
    Formalism.L2.Th1.B.constantCoeff_fExp (map_zero _)
  have hne : Formalism.L2.Th1.B.fExp (0 : MvPowerSeries Unit K) ≠ 0 := by
    intro h0; rw [h0, map_zero] at hc; exact zero_ne_one hc
  exact (mul_left_cancel₀ hne (h.symm.trans (mul_one _).symm))

theorem oneUnit_fExp_neg {f : PowerSeries K} (h : Formalism.InvariantFactorPaths.G7.Simeq (ι := Unit) f 0) :
    OneUnit (Formalism.L2.Th1.B.fExp (-f)) := by
  obtain ⟨h0, hI⟩ := h
  rw [sub_zero] at h0 hI
  have h0n : MvPowerSeries.constantCoeff (-f : MvPowerSeries Unit K) = 0 := by
    rw [map_neg, h0, neg_zero]
  have hf : OneUnit (Formalism.L2.Th1.B.fExp f) :=
    ⟨Formalism.L2.Th1.B.constantCoeff_fExp h0, (Ser.intS_iff_integral _).2 hI⟩
  refine Ser.oneUnit_of_mul_eq_one hf ?_
  rw [← Formalism.L2.Th1.B.fExp_add h0 h0n, add_neg_cancel]
  exact fExp_zero

end Two

theorem theta_from_phi_derivative : ThetaZeroFromPhiDerivative := by
  intro l _ L ι W hU hW ω₀ hω hω2 hx hS s N hN hlN hs
  refine shiftAnalyticW l L ι W hU hW ω₀ hω hω2 hx ?_ s N hN hlN hs
  rw [even_theta_half_period_in_model l L ι W hU ω₀ hω hω2]
  exact Two.oneUnit_fExp_neg hS

end Formalism.L2.Th1.E
