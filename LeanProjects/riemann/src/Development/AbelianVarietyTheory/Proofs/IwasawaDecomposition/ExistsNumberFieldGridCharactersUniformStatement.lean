import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNumberFieldGridCharactersUniform
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_numberField_gridCharacters_uniform : ∀ (cDep b : ℝ) (B₀ : Pre), ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ (s : Stages), s.B.toPre = B₀ → 0 < GlobalTheory.ChiGrid.q0 s.toD7 → ∀ (T : Type) (L : Formalism.IndefR.Links.LevCh s.toD7 T) (_G : GlobalTheory.ChiGrid.GridData L ⟨1, cDep, b⟩), ∃ G' : GlobalTheory.ChiGrid.GridData L ⟨1, cDep, b⟩, GlobalTheory.BigTop.Fun.FieldHas G' M.val.toRingHom := by
  first | exact @GlobalTheory.GridField.exists_field_uniform | exact GlobalTheory.GridField.exists_field_uniform | (intros; apply GlobalTheory.GridField.exists_field_uniform <;> assumption)
