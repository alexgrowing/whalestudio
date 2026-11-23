import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.VdEqVJof

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

theorem jordan_splitting_exists : JordanExists := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs
  exact ⟨fun X L hnd hL hLi 𝔭 h𝔭 => G1.jordan_exists hK hF hs X L hnd hL hLi 𝔭 h𝔭,
    fun L _ 𝔭 h𝔭 b a hJ => G1.vd_eq_vJof hK hF L 𝔭 h𝔭 b a hJ⟩

end Formalism.L2.SG.Pf.Cnt
