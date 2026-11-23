import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetCosetRepsBoundedHalfPoints
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSBArgs
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MeasureTheory ValuativeRel
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StepData GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finset_cosetReps_bounded_half_points : ∀ {D : D7} {a b : ℕ} (β' : GL (Fin b) (Lev.EAf D)) (β : GL (Fin a) (Lev.EAf D)) (P : Finset (Pl D.host.E)) (e : AE D) (n : ℕ), IsIdemSum e P → ∃ R : Finset (Mx D b a), (∀ r ∈ R, IsHalf e r ∧ IsSmall P β' β (-(n : ℤ)) r) ∧ (∀ t, IsHalf e t → IsSmall P β' β (-(n : ℤ)) t → ∃ r ∈ R, IsSmall P β' β n (t - r)) ∧ ∀ r ∈ R, ∀ r' ∈ R, IsSmall P β' β n (r - r') → r = r' := by
  first | exact @GlobalTheory.FunObj.exists_finset_cosetReps | exact GlobalTheory.FunObj.exists_finset_cosetReps | (intros; apply GlobalTheory.FunObj.exists_finset_cosetReps <;> assumption)
