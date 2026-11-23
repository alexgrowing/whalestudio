import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IqBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CycInertia
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

theorem UpperTheory.V.Loc.frobCyc :
    ∀ (l : ℕ) [Fact l.Prime], ∃ σ : GQ l, IsFrob σ ∧ cyc l l σ = 1 := by
  intro l _
  obtain ⟨-, -, -, ⟨σ, hσ⟩, h⟩ := iqBasic l
  obtain ⟨g, hg, hc⟩ := (cycInertia l).1 (cyc l l σ)⁻¹
  refine ⟨σ * g, (h σ _ hσ).2 ?_, ?_⟩
  · rwa [inv_mul_cancel_left]
  · rw [map_mul, hc, mul_inv_cancel]
