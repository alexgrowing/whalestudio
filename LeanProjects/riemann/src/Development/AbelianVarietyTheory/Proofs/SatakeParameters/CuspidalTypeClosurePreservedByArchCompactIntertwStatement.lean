import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalTypeClosurePreservedByArchCompactIntertw
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BarKHomSurjective
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
open NumberField GlobalTheory.CuspRep GlobalTheory.Published GlobalTheory.IdemAdj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_typeClosure_preserved_by_archCompact_intertwiner : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ₀ : Representation ℂ (Kinf E a) W) (U : Submodule ℂ π.V), FiniteDimensional ℂ U → (∀ k, ∀ u ∈ U, cptOn π k u ∈ U) → ∀ f : π.V →ₗ[ℂ] π.V, (∀ k, ∀ u ∈ U, f (cptOn π k u) = cptOn π k (f u)) → ∀ u ∈ U, (∀ g, (fun k : Kinf E a => (cptRep E a k u.1).1 g) ∈ AutFin.coeffSpan ρ₀) → ∀ g, (fun k : Kinf E a => (cptRep E a k (f u).1).1 g) ∈ AutFin.coeffSpan ρ₀ := by
  first | exact @GlobalTheory.IdemAdj.typeClosure_of_intertwine | exact GlobalTheory.IdemAdj.typeClosure_of_intertwine | (intros; apply GlobalTheory.IdemAdj.typeClosure_of_intertwine <;> assumption)
