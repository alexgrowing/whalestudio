import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Ksph

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_subgroup_ksph : ∀ (D : D7) (V : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))),
    ∃ K : Subgroup (GA D V), (K : Set (GA D V)) = KsphC V S ∧ ∀ S', S ⊆ S' → KsphC V S' ⊆ KsphC V S :=
  fun _ V S => ⟨_, (GlobalTheory.AutFunCompare.KsphC_eq V S).symm,
    fun _ hS _ hg => ⟨hg.1, hg.2.1, fun v hv => hg.2.2 v (hS hv)⟩⟩

end GlobalTheory.Mem.Ksph
