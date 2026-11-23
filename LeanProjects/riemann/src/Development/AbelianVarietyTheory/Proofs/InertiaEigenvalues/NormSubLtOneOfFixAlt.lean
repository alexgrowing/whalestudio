import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTopologicalClosureZpowersSupInertia

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.PtCore

namespace GlobalTheory.UnramInertia

theorem norm_sub_lt_one_of_fix : ∀ (l : ℕ) [Fact l.Prime] (σ : GQ l), (∀ x ∈ MaximalUnramifiedExtension l, σ x = x) →
    ∀ x : Om l, ‖x‖ ≤ 1 → ‖σ x - x‖ < 1 := by
  intro l _ σ hσ x hx
  have hmem : σ ∈ (MaximalUnramifiedExtension l).fixingSubgroup := by
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).2 hσ
  exact GlobalTheory.FrobGen.norm_sub_lt hmem x hx

end GlobalTheory.UnramInertia
