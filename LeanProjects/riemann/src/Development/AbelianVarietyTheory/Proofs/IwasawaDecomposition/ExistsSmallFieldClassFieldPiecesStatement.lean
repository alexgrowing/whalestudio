import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmallFieldClassFieldPieces
import Formalism.LocalToGlobal.HilbertRowConditions.KaTiedIffKapDef
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.HostPins
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host Formalism.L2.Rows GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smallField_classFieldPieces : GlobalArtinReciprocity → WeberRayFieldSt → ∀ (X : Stages) (f : Fr X.B.toPre) (δ : FieldDat X.B.toPre) (T : HostTied X.toD7), ∃ P : KsPieces X.toD7 T, P.HK = qb T.fr.ι (hilbertField X.B.host.d δ.jField) ∧ P.rcf = qb T.fr.ι δ.ray ∧ P.M = qb T.fr.ι δ.M ∧ P.MDel = qb T.fr.ι δ.M' ∧ P.KPs = qb T.fr.ι (⨆ j ∈ Set.Icc 1 X.B.R.m, δ.KPsi j) := by
  first | exact @GlobalTheory.SmallFieldPieces.exists_pieces | exact GlobalTheory.SmallFieldPieces.exists_pieces | (intros; apply GlobalTheory.SmallFieldPieces.exists_pieces <;> assumption)
