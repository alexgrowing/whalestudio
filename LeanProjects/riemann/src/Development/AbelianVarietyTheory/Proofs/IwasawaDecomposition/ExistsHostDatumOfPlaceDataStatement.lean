import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHostDatumOfPlaceData
import Formalism.LocalToGlobal.UnitaryNorms.DatumS
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host GlobalTheory.Published GlobalTheory.Mem.HD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hostDatum_of_place_data : GlobalArtinReciprocity → ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (T : LinkedFamilyData ex), HostPins D ex.nch → ∀ B : PlacesOverCommonPrime D.host, ∃ hd : HostDatumC T, hd.d3b = B := by
  first | exact @GlobalTheory.HostDatumExists.exists_hostDatum | exact GlobalTheory.HostDatumExists.exists_hostDatum | (intros; apply GlobalTheory.HostDatumExists.exists_hostDatum <;> assumption)
