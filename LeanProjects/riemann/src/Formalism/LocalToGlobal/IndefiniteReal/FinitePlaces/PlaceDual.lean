import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SplitInt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceLatDualIiiOf
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceDualB
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ExistsNatIntFMat
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceDualBIv

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.Datum

theorem placeLatDual_of {D : D7} (hL : LatSelfDual D) : PlaceLatDual D := by
  intro ψ hψ S T ΛS ΛT hS hT
  refine ⟨fun e' he' u hu => latO_map_splitIdem S T ΛS ΛT he' hu,
    fun e' he' g h hg hh => PDB.placeLatDualVi D ψ hψ S T ΛS ΛT hS hT e' he' g h hg hh,
    fun P e he => ⟨PDA.placeLatDualIi_of hL ψ hψ S T ΛS ΛT hS hT P e he,
      PDA.placeLatDualIii_of hL ψ hψ S T ΛS ΛT hS hT P e he,
      PDB.placeLatDualIv D ψ hψ S T ΛS ΛT hS hT P e he,
      PDB.placeLatDualV D ψ hψ S T ΛS ΛT hS hT P e he⟩⟩

end Formalism.IndefR.Fin

end
