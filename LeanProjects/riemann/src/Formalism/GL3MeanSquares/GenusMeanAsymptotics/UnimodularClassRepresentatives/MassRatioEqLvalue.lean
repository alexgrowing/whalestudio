import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CovolumeIntegerLatticeEq
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LValEtaEqLValEtaF
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.DifferentIdealEqTop

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem massRatio_pos (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (M : ℕ) (hM : 2 ≤ M) :
    0 < Formalism.HermitianLatticesTheory.massRatioRightSide K M := by
  have hv := vInv_pos K
  unfold Formalism.HermitianLatticesTheory.massRatioRightSide
  refine mul_pos (div_pos (pow_pos (mul_pos ?_ (pow_pos (div_pos hv Real.pi_pos) _)) _) ?_)
    (lValEta_pos hK M hM)
  · exact_mod_cast Nat.factorial_pos _
  · exact Real.sqrt_pos.mpr (pow_pos (mul_pos two_pos hv) _)

theorem massRatio_eq_lvalue (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (m : ℕ) (hm : 2 ≤ m) :
    Formalism.HermitianLatticesTheory.massRatioRightSide K m =
      (((m - 1).factorial : ℝ) / Real.pi ^ m) ^ Formalism.HermitianLatticesTheory.fDeg K *
        Formalism.HermitianLatticesTheory.vInv K ^ (Formalism.HermitianLatticesTheory.fDeg K * m) /
          Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) * lValEtaF K F m := by
  unfold Formalism.HermitianLatticesTheory.massRatioRightSide
  rw [lValEta_eq_lValEtaF hK hF m hm, mul_comm (Formalism.HermitianLatticesTheory.fDeg K) m, pow_mul, ← mul_pow, div_pow]
  congr 3
  ring

end Formalism.HermitianLattices.Ext.L3
