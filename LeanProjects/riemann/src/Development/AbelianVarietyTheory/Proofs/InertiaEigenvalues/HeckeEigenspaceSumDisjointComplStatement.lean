import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeEigenspaceSumDisjointCompl
import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverEta
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeEigenspaceSum_disjoint_compl : ∀ (D : D7) (i : D.nd.Loc) (Y : Set (D.nd.X i)), Disjoint (D.nd.eigSum i Y) (D.nd.eigSum i Yᶜ) := by
  first | exact @GlobalTheory.EtaJoin.eigSum_disjoint_compl | exact GlobalTheory.EtaJoin.eigSum_disjoint_compl | (intros; apply GlobalTheory.EtaJoin.eigSum_disjoint_compl <;> assumption)
