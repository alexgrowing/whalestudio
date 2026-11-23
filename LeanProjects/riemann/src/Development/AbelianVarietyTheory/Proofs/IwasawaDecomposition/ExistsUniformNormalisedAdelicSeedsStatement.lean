import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformNormalisedAdelicSeeds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteNonzeroIndexPlacesReferenceTuple
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniform_normalisedAdelicSeeds : ∀ (K : Ctx) (P : Pre) (f : GlobalTheory.Mem.Top.Fr P) (F : IntermediateField ℚ ℂ), ∃ (S : Finset ℕ) (S₂ : Finset ℂ), (∀ z ∈ S₂, IsAlgebraic ℚ z) ∧ ∀ px : PreX P, (∃ F₀, SeedW K P f F F₀ px Set.univ ⊤) → ∃ F₀, SeedW K P f F F₀ px (S : Set ℕ) (IntermediateField.adjoin ℚ (S₂ : Set ℂ)) := by
  first | exact @GlobalTheory.Mem.R3.Rw.Resize.seeds_uniform_exists | exact GlobalTheory.Mem.R3.Rw.Resize.seeds_uniform_exists | (intros; apply GlobalTheory.Mem.R3.Rw.Resize.seeds_uniform_exists <;> assumption)
