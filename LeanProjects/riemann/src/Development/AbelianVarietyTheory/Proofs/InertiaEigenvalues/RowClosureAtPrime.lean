import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.ElevenLe
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowClosureLinkingStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem linkN_at : Hypotheses₂ → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : GlobalTheory.Mem.Top.Bl.Prm hL) (C : ℝ) (CT : ℕ), 0 ≤ C → GlobalTheory.Fc.RL.At p (fun S L => GlobalTheory.Fc.RowE S L fun _ D O _ _ => GlobalTheory.NFacts.Facts D O.ex.nch) → GlobalTheory.Fc.RL.At p (fun S L => GlobalTheory.Fc.RowE S L fun _ D _ _ _ => Extra D C CT) → GlobalTheory.Fc.RL.At p (fun S L => GlobalTheory.Fc.R1.PredicateAtBundlePoints S L fun 𝒞 => Closed 𝒞 fun Fm _ => BoundAtTwoAndThreeForFamily Fm) → GlobalTheory.Fc.RL.At p (fun S L => GlobalTheory.Fc.R1.PredicateAtBundlePoints S L fun 𝒞 => Closed 𝒞 fun Fm _ => Formalism.MainNotions.LinkN Fm) := by
  intro hP hL p C CT hC h1 h2 h3
  obtain ⟨R1, r1, e1⟩ := h1
  obtain ⟨R2, r2, e2⟩ := h2
  obtain ⟨R3, r3, e3⟩ := h3
  refine ⟨_, r1.and (r2.and r3), ?_⟩
  refine GlobalTheory.T.row_closure_linking hP _ _ C CT hC ?_ ?_
  · exact (GlobalTheory.Fc.RowE.and
      (GlobalTheory.Fc.EvP.mono (fun _ _ _ H β q => H β ⟨q.1, q.2.1⟩) e1)
      (GlobalTheory.Fc.EvP.mono (fun _ _ _ H β q => H β ⟨q.1, q.2.2.1⟩) e2))
  · exact GlobalTheory.Fc.Row.strengthen (fun _ _ _ _ _ t => ⟨t.1, t.2.2.2⟩) e3

end GlobalTheory.NLink
