import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatOAnnIffOf
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.GlobalDual
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatSDa
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceDual

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.Datum

theorem latSelfDual (D : D7) : LatSelfDual D := by
  intro ψ hψ S T ΛS ΛT hS hT
  exact ⟨latO_isCompact S T ΛS ΛT hS hT, latO_isOpen S T ΛS ΛT hS hT,
    fun a ha u hu => latO_smul_mem S T ΛS ΛT ha hu,
    fun x hx => latO_ann_iff_of hψ S T hS hT (latO_nsmul_mem S T ΛS ΛT hS hT)
      (fun γ h => PDA.globalDual S T hS hT γ h) x hx⟩

theorem placeLatDual (D : D7) : PlaceLatDual D := placeLatDual_of (latSelfDual D)

end Formalism.IndefR.Fin

end
