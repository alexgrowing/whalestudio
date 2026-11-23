import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyLocalisedFormsTypeSectionHecke
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_localised_forms_type_section_hecke : ∀ (D : D7) (M : MtFam D) (i : D.nd.Loc), HeckeTied D M → HeckeRational D M → AVTied D M → GlobalTheory.EtaJoin.SplitUnif D → GlobalTheory.EtaJoin.HeckeScalar M i → Nonempty (Sec D i) := by
  first | exact @GlobalTheory.PendOf.SecProof.main | exact GlobalTheory.PendOf.SecProof.main | (intros; apply GlobalTheory.PendOf.SecProof.main <;> assumption)
