import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArchimedeanUnitaryPointsEquivUnitaryGroup
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (τ : E →+* ℂ), ∃ e : embU n τ ≃ₜ* Matrix.unitaryGroup (Fin n) ℂ, ∀ x : embU n τ, GlobalTheory.Branching.unitaryIncl n (e x) = cEmb τ (x : UA E n) := by
  first | exact @GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup | exact GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup | (intros; apply GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup <;> assumption)
