import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanExists
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscEquiv

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.G2

theorem jordan_invariants_holds : JordanInv := by
  intro K F V V' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _hK hF h h' _hs _hs' X X' L L' hL hL' 𝔭 h𝔭 b a b' a'
    hJ hJ' hiso j
  obtain ⟨f⟩ := hiso
  obtain ⟨g⟩ := disc_equiv hF h𝔭 hL hJ.1 hJ.2.1 hJ.2.2.1 hJ.2.2.2.1 hJ.2.2.2.2
  obtain ⟨g'⟩ := disc_equiv hF h𝔭 hL' hJ'.1 hJ'.2.1 hJ'.2.2.1 hJ'.2.2.2.1 hJ'.2.2.2.2
  have hc := card_quot_smul_top_congr ((g.symm.trans f).trans g') (extP K 𝔭 ^ j)
  rw [card_pi_quot, card_pi_quot] at hc
  exact Nat.pow_right_injective (two_le_absNorm h𝔭) hc

end Formalism.L2.SG.Pf.Cnt
