import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeSpaceProjectionToPointEigenspaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.typeSpace_projection_to_pointEigenspaces : ∀ (D : D7) (M : MtFam D) (i : D.nd.Loc), HeckeTied D M → HeckeRational D M → AVTied D M → SplitUnif D → HeckeScalar M i → D.nd.EigSpan → TypeTie D i := by
  first | exact @GlobalTheory.EtaJoin.TypeTieProof.typeTie_holds | exact GlobalTheory.EtaJoin.TypeTieProof.typeTie_holds | (intros; apply GlobalTheory.EtaJoin.TypeTieProof.typeTie_holds <;> assumption)
