import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalB
import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementC

noncomputable section

namespace Formalism.L2.Th1.B.Cor

open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 swap2 DivAB)

theorem even_phi_simeq_odd_phi : PhESimPhO := by
  intro K _ _ _ g2 g3 s2 c0 e1 P l i ep F hP he hF hC hc h2
  exact simeqHalf K Unit _ _ h2 ((diffPh K g2 g3 s2 c0 e1 P l i ep F hP he hF hC).2 hc)

theorem sigma_one_cocycle_shifted : SigmaOneCocycleShifted := by
  intro K _ _ _ g2 g3 s2 c0 e1 P l i ep F hP he hF hi hC hc hk h2
  have hW := wOfWp K g2 g3 e1 P hP he
  have hw := (wIntegral K c0 e1 P l i ep F hF hC hc).2
  obtain ⟨a, -, b, c⟩ := f1E K (3 * e1) (3 * e1 ^ 2 - g2 / 4) e1 s2 (wOf e1 P) l i F hW hF hi hk hw h2
  exact ⟨a, b, c⟩

theorem cc_Dinv {K : Type} [Field K] [CharZero K] (l f : PowerSeries K)
    (h1 : PowerSeries.coeff 1 l = 1) :
    PowerSeries.constantCoeff (Dinv l f) = PowerSeries.coeff 1 f := by
  have key : ∀ g : PowerSeries K, PowerSeries.constantCoeff (PowerSeries.derivative K g) =
      PowerSeries.coeff 1 g := by
    intro g
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
    simp
  unfold Dinv
  rw [map_mul, PowerSeries.constantCoeff_inv, key, key, h1, inv_one, one_mul]

theorem first_jet_of_formal_law : JetOne := by
  intro K _ _ _ l i f hl0 hl1 hi hS
  obtain ⟨hi0, -, hil⟩ := hi
  obtain ⟨hg0, hE⟩ := hS
  have hi1 : PowerSeries.coeff 1 i = -1 := by
    have e := law_coeff_one_subst l i hi0
    rw [hil, map_neg, hl1, one_mul] at e
    exact e.symm
  have hE1 : PowerSeries.coeff 1
      (PowerSeries.subst (PowerSeries.subst i f - f : PowerSeries K) (PowerSeries.exp K) :
        PowerSeries K) = PowerSeries.coeff 1 (PowerSeries.subst i f - f : PowerSeries K) := by
    rw [law_coeff_one_subst _ _ hg0, PowerSeries.coeff_exp]
    simp
  have hn : ‖PowerSeries.coeff 1 (PowerSeries.subst i f - f : PowerSeries K)‖ ≤ 1 := by
    rw [← hE1]
    exact hE (Finsupp.single () 1)
  rw [map_sub, law_coeff_one_subst f i hi0, hi1] at hn
  rw [cc_Dinv l f hl1, ← norm_neg]
  have : -(2 * PowerSeries.coeff 1 f) = PowerSeries.coeff 1 f * -1 - PowerSeries.coeff 1 f := by
    ring
  rw [this]
  exact hn

theorem jets_of_odd_parallelogram_phi : JetsPhO := by
  intro K _ _ _ g2 g3 s2 c0 P l i ep F hP hF hi hC h2 n hn
  rcases hn with rfl | hn
  · have hS := phOEven K s2 P l i hP.2.1 hF.2.2.1 hF.2.2.2.1 hi
    have h := first_jet_of_formal_law K l i _ hF.2.2.1 hF.2.2.2.1 hi hS
    rw [norm_mul, h2, one_mul] at h
    exact h
  · exact jetsThree K F l _ hF (f1O K g2 g3 s2 c0 P l i ep F hP hF hi hC h2).2.2.1 n hn

end Formalism.L2.Th1.B.Cor
