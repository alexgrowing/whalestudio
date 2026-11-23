import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicIwasawaMaximalParabolicFiniteReps
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicIwasawa_maximalParabolic_finiteReps : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a r : ℕ) (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) → ∃ T : Finset (GL (Fin a) (Af E)), ∀ g : GA E a, ∃ (y : BlockIx a r → Ad E) (m : GA E a), (∀ i j : Fin a, ((i : ℕ) < r ↔ (j : ℕ) < r) ∨ m.1 i j = 0) ∧ ∃ t ∈ T, ∃ k : Kinf E a, ∃ l ∈ L, g = unip y * m * finGL E a t * infGL E a (Unitary.toUnits k) * finGL E a l := by
  first | exact @GlobalTheory.IwaParab.iwasawa_parab | exact GlobalTheory.IwaParab.iwasawa_parab | (intros; apply GlobalTheory.IwaParab.iwasawa_parab <;> assumption)
