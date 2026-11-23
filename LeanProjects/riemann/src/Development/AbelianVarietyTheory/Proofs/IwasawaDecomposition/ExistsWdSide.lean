import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyWdSideOfTie

noncomputable section
namespace GlobalTheory.HeightCounting
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem exists_wdSide : GlobalTheory.Published.DeRhamPotSemistable → ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), Nonempty (WDSide D T) :=
  fun hB D T => nonempty_wdSide_of_tie hB D T

end GlobalTheory.HeightCounting
end
