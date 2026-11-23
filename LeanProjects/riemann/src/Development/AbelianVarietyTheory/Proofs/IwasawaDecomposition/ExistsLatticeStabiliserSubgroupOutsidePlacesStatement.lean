import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeStabiliserSubgroupOutsidePlaces
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_stabiliser_subgroup_outside_places : ∀ (D : D7) (V : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))), ∃ K : Subgroup (GA D V), (K : Set (GA D V)) = KsphC V S ∧ ∀ S', S ⊆ S' → KsphC V S' ⊆ KsphC V S := by
  first | exact @GlobalTheory.Mem.Ksph.exists_subgroup_ksph | exact GlobalTheory.Mem.Ksph.exists_subgroup_ksph | (intros; apply GlobalTheory.Mem.Ksph.exists_subgroup_ksph <;> assumption)
