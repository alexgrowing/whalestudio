import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bridge
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open Formalism.IndefR.Bridge Formalism.L2.DIV Formalism.DivisionValues Formalism.L2.Col NumberField MeasureTheory Polynomial

namespace GlobalTheory.EigTransfer

theorem linearMap_ext_of_iSup_eq_top {E F C : Type} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (Ec : C → Submodule ℂ E) (htop : (⨆ c, Ec c) = ⊤) (f g : E →ₗ[ℂ] F)
    (h : ∀ c, ∀ w ∈ Ec c, f w = g w) : f = g := by
  have hle : (⊤ : Submodule ℂ E) ≤ LinearMap.eqLocus f g := by
    rw [← htop]
    exact iSup_le fun c w hw => LinearMap.mem_eqLocus.2 (h c w hw)
  ext e
  exact LinearMap.mem_eqLocus.1 (hle Submodule.mem_top)

end GlobalTheory.EigTransfer
