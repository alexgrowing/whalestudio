import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.KerOne

noncomputable def iw0 {D : D7} {H : Formalism.L2.Herm.HermColsCh D} (G : Formalism.L2.Herm.SymmetricGroupCompatibility D H) (u : D.what₂.Word) (v : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar v)) (q : Fin (D.gat u v hg).P.nV) :
    D.host.E →+* (D.gat u v hg).P.Qq q :=
  ((G u v hg).eQ q _ rfl).symm.toRingHom.comp
    (((RingHom.fst _ _).comp ((G u v hg).spl _ ((G u v hg).pl q).2).toRingHom).comp
      (Formalism.UG.inclE (F := D.host.F) ((((G u v hg).pl q).1).adicCompletion D.host.F)))

theorem splitPlaceIdempotent_cmEmbedding_compat {D : D7} {H : Formalism.L2.Herm.HermColsCh D} (G : Formalism.L2.Herm.SymmetricGroupCompatibility D H) (u : D.what₂.Word) (v : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar v)) (q : Fin (D.gat u v hg).P.nV) (x : D.host.E) :
    (G u v hg).eQ q _ rfl (iw0 G u v hg q x) =
      ((G u v hg).spl _ ((G u v hg).pl q).2
        (Formalism.UG.inclE (F := D.host.F) ((((G u v hg).pl q).1).adicCompletion D.host.F) x)).1 := by
  simp [iw0]

end GlobalTheory.Mem.Top.KerOne
