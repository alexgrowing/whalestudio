import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.Columns.HeckeSp
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_hyperspecial_trivialCharacter_splits_off_places : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank), Formalism.IndefR.Lev.IsBaseFrame V β Λ N → (∀ k ∈ Formalism.IndefR.Lev.levG V β L, ∃ n : ℕ, 0 < n ∧ Formalism.IndefR.Lev.levChi V β L k ^ n = 1) ∧ ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, IsPrimeIdem P e f → ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → (∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) → (∀ g, SuppF V f g → (g ∈ Formalism.IndefR.Lev.levG V β L ↔ g ∈ KsphC V ∅)) ∧ (∀ g ∈ Formalism.IndefR.Lev.levG V β L, SuppF V f g → Formalism.IndefR.Lev.levChi V β L g = 1) ∧ ∀ k ∈ Formalism.IndefR.Lev.levG V β L, ∃ k₁ ∈ Formalism.IndefR.Lev.levG V β L, ∃ k₂ ∈ Formalism.IndefR.Lev.levG V β L, SuppF V f k₁ ∧ SuppF V (1 - f) k₂ ∧ k = k₁ * k₂ := by
  first | exact @GlobalTheory.LevSplit.lev_split | exact GlobalTheory.LevSplit.lev_split | (intros; apply GlobalTheory.LevSplit.lev_split <;> assumption)
