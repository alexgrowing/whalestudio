import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChiDetSplitCentre

open NumberField

namespace GlobalTheory.SplitCentreChar

theorem exists_hChar_splitCentre : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (d : ℕ), 0 < d →
    ∀ s : ℂ, ∃ χ : Formalism.L2.Host.HChar E, ∀ t : ℝ,
      ((GlobalTheory.CuspRep.chiDet d χ (GlobalTheory.UnitaryBC.splitCentre E d t) : ℂˣ) : ℂ) = Complex.exp (-(t * s)) := by
  intro E _ _ _ d hd s
  obtain ⟨χ, hχ⟩ := GlobalTheory.CuspQuot.exists_chiDet_splitCentre (E := E) hd (-s)
  exact ⟨χ, fun t => by rw [hχ t]; congr 1; ring⟩

end GlobalTheory.SplitCentreChar
