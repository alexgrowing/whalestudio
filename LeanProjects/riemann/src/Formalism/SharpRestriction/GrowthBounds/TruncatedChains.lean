import Formalism.SharpRestriction.GrowthBounds.GLWeightTheory
import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.RaisingKillOfInterface
import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.RestPairOf
import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.ProjectorFactorMemWeightSpace
import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.YbatBase
import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.YbatStep
import Formalism.SharpRestriction.GrowthBounds.TruncatedChains.CnNODrop

namespace Formalism.MainNotions.G.ExtremalProjector

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

theorem restYB (D : Formalism.BasicNotions.D7) : RestYB :=
  restYB_of (ybat_base D restKill restPair (restPair'_of restPair)) ybat_symm

theorem raising_operators_kill_image (D : Formalism.BasicNotions.D7) : SimpleRaisingKillsExtremalProjector :=
  raising_kill_of_interface restConn restComm (restYB D) restKill

theorem extremal_projector_statement (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.CovariantDegrees.adm5 D := sizes_bound_of_log_estimates D (raising_operators_kill_image D)

end Formalism.MainNotions.G.ExtremalProjector
