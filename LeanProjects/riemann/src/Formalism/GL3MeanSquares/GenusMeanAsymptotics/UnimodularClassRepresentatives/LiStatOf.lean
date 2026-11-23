import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.RepRatioEqZero
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LiPin
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatioHolds

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

theorem liStat_of (hR : LIRatio) (hP : LIPin) : LIStat := by
  intro K F _ _ _ _ _ _ hK hF V V' _ _ _ _ _ _ _ _ _ _ h h' S L 𝔭 n hs hd h𝔭 hn hx hL hLi
  obtain ⟨L₀, hL₀, hL₀i, hR0, hpin⟩ := hP K F hK hF V V' h h' S 𝔭 n hs hd h𝔭 hn hx
  have hrat := hR K F hK hF V V' h h' S L L₀ 𝔭 n hs hd h𝔭 hn hx hL hLi hL₀ hL₀i
  rw [hpin] at hrat
  have key : psiP S L 𝔭 = (Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K V - 1) * vF 𝔭 n) *
      alphaStd K 𝔭 (finrank K V - 1) * repRatio h L 𝔭 n := by
    apply mul_right_cancel₀ hR0
    rw [hrat]
    ring
  rw [key, repRatio, Nat.mul_add, pow_add]
  ring

theorem liStat : LIStat := liStat_of liRatio liPin

end Formalism.HermitianLattices.Ext.L3
