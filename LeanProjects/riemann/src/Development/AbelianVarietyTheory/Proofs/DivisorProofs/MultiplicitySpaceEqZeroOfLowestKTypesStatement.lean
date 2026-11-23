import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypes
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicitySpace_eq_zero_of_lowestKTypes : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (θ : InfFam D), IsInfFam θ → (∀ τ, lowT M τ ≠ ⊥) → ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ Mult θ M J χ, (∀ v : ∀ ρ, lowT M ρ, T (fun ρ => v ρ) = 0) → T = 0 := by
  first | exact @GlobalTheory.LowTypeDetermined.eq_zero_of_lowT | exact GlobalTheory.LowTypeDetermined.eq_zero_of_lowT | (intros; apply GlobalTheory.LowTypeDetermined.eq_zero_of_lowT <;> assumption)
