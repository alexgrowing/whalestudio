import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.ElevenLe
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConclusionOfFamilyFactsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinkNAlongFamilyOfLocalBoundsStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem linkN_row : Hypotheses₂ → ∀ (Q : GlobalTheory.Mem.Top.V4.Slot) (Lk : GlobalTheory.Fc.LkT GlobalTheory.Fc.Bundle) (C : ℝ) (CT : ℕ), 0 ≤ C →
    GlobalTheory.Fc.RowE Q Lk (fun _ D O _ _ => GlobalTheory.NFacts.Facts D O.ex.nch ∧ Extra D C CT) →
    GlobalTheory.Fc.R1.PredicateAtBundlePoints Q Lk (fun 𝒞 => Closed 𝒞 fun Fm _ => BoundAtTwoAndThreeForFamily Fm) →
    GlobalTheory.Fc.R1.PredicateAtBundlePoints Q Lk (fun 𝒞 => Closed 𝒞 fun Fm _ => Formalism.MainNotions.LinkN Fm) := by
  intro hP Q Lk C CT hC hE h23
  refine ((GlobalTheory.Fc.RowE.row hE).and h23).imp fun 𝒜 σ _ hh => ?_
  obtain ⟨hA, ε1, hε, hcl⟩ := hh
  refine ⟨ε1, hε, fun e he hle => ?_⟩
  obtain ⟨K, hK⟩ := hcl e he hle
  refine ⟨K, fun Fm CH hc hL => ?_⟩
  have hF : FactsF Fm C CT := fun x hx i => hA Fm (GlobalTheory.Cp.d3_a hc) x hx i
  exact GlobalTheory.T.linkN_along_family_of_localBounds Fm (GlobalTheory.T.conclusion_of_family_facts hP Fm C CT hC hc.1.2 hF (hK Fm CH hc hL))

end GlobalTheory.NLink
