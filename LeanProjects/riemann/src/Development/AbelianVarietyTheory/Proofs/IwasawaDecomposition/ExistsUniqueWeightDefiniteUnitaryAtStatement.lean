import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueWeightDefiniteUnitaryAt
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_weight_definiteUnitary_at : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AU E n) (τ : E →+* ℂ), ∃! lam : DomWeight n, π.HasWt τ lam := by
  first | exact @GlobalTheory.DefU.AU.existsUnique_hasWt | exact GlobalTheory.DefU.AU.existsUnique_hasWt | (intros; apply GlobalTheory.DefU.AU.existsUnique_hasWt <;> assumption)
