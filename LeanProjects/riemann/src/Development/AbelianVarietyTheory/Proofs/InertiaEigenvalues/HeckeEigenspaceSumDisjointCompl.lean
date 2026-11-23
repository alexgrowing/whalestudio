import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverEta
import Formalism.SharpRestriction.LevelLetterCocycles.CongruenceSingleEndomorphism
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

namespace GlobalTheory.EtaJoin

theorem eigSum_disjoint_compl : ∀ (D : D7) (i : D.nd.Loc) (Y : Set (D.nd.X i)),
    Disjoint (D.nd.eigSum i Y) (D.nd.eigSum i Yᶜ) := by
  intro D i Y
  exact (Formalism.MainNotions.PairedCharacterCondition.CongruenceModules.heckeEig_indep (D.nd.T i) (D.nd.act i) (D.nd.T_sep i)).disjoint_biSup_biSup
    disjoint_compl_right

end GlobalTheory.EtaJoin
