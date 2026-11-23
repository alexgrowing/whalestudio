import Formalism.LocalToGlobal.AdelicCompactOpens.UniROfUniRT
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightDualUniqueness.SelfInjective

open NumberField ReciprocityTheory.Aut Formalism.L2.NG

namespace PI.UnitaryGroupMassFormula.AlgWtDualUniq

theorem main (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) : Formalism.L2.Props.DualUnique L n := by

  have fd : ∀ c : AlgWt L n, FiniteDimensional ℂ c.W := by
    intro c
    have h := c.alg
    unfold Formalism.AUTREP.IsAlgWeight at h
    exact h.1
  intro a b b' h1 h2
  obtain ⟨B, hB0, hB⟩ := h1
  obtain ⟨C, hC0, hC⟩ := h2
  haveI := fd a
  haveI := fd b
  haveI := fd b'
  haveI : a.ρ.IsIrreducible := a.irr
  haveI : b.ρ.IsIrreducible := b.irr
  haveI : b'.ρ.IsIrreducible := b'.irr
  exact dual_unique B hB hB0 C hC hC0

end PI.UnitaryGroupMassFormula.AlgWtDualUniq
