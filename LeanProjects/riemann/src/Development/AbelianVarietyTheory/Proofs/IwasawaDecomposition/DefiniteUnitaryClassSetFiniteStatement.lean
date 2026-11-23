import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitary_classSet_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (K : Subgroup (finU E n)), IsOpen (K : Set (finU E n)) → ∃ S : Finset (UA E n), ∀ g : UA E n, ∃ γ ∈ ratU E n, ∃ s ∈ S, ∃ x ∈ infU E n, ∃ k ∈ K, g = γ * s * x * (k : UA E n) := by
  first | exact @GlobalTheory.DefU.ClassFin.classSet_finite | exact GlobalTheory.DefU.ClassFin.classSet_finite | (intros; apply GlobalTheory.DefU.ClassFin.classSet_finite <;> assumption)
