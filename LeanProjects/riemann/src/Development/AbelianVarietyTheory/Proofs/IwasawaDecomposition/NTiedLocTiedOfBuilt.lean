import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyAllIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormEqOneOfVEqZero

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting
  NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.HeightCounting

theorem locTied_any (D' : D7) : Nonempty (Formalism.L2.LocTied D') :=
  ⟨⟨fun l _ => GlobalTheory.LocArith.arithTied l (D'.loc l), fun i w hw => D'.nbr_ind i w hw,
    fun i w hw => D'.ntwbr_ind i w hw⟩⟩

theorem nTied_locTied_of_built : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL), CgCmp hL → ∀ (D' : D7) (b : NBuilt hL D'),
    Nonempty (NormalizedHeckeDataPlaceholder D') ∧ Nonempty (Formalism.L2.LocTied D') := by
  intro hL hcg D' b
  exact ⟨⟨⟨⟩⟩, locTied_any D'⟩

end GlobalTheory.HeightCounting

end
