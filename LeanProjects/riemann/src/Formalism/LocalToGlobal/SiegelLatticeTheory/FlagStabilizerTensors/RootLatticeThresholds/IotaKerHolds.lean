import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.IotaKerCore
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.XLeSpanEXLam
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.AmpIota
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.UnipotentInLevelSubgroup

namespace Formalism.L2.SG.Pf.KernelOfEmbedding

theorem IotaKer_holds : Formalism.L2.SG.Pf.FinXP.IotaKer := by
  intro D X Y u u' s₁ s₂ t₁ t₂ n₁ n₂ m₁ m₂ c₁ c₂
  exact iotaKer_core (Formalism.L2.SG.Closed.NeatKu_holds X u' Y.hK) Formalism.L2.SG.Pf.iotaRepC_holds s₁ s₂ t₁ t₂ n₁ n₂ m₁ m₂ c₁ c₂

end Formalism.L2.SG.Pf.KernelOfEmbedding
