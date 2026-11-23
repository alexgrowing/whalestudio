import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAutomorphicSideEmptyLocal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_automorphic_side_empty_local : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7), IsEmpty D.nd.Loc → ∀ T : GlobalTheory.RowTie.WDTie D.nd D.naut, ∃ (C : NBC D.naut) (A : AUSide (setBC D C)), AUTrue hL (setBC D C) T A := by
  first | exact @GlobalTheory.AutQuot.exists_nbc_auSide | exact GlobalTheory.AutQuot.exists_nbc_auSide | (intros; apply GlobalTheory.AutQuot.exists_nbc_auSide <;> assumption)
