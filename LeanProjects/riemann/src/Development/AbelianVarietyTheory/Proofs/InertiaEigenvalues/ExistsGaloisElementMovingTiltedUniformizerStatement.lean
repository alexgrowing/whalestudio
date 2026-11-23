import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisElementMovingTiltedUniformizer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanOfPowMul
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_element_moving_tilted_uniformizer : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e), l ≠ 2 → ∃ (g : Gl l) (ε : OCb l) (c : ℕ), IsEps ε ∧ c ≠ 0 ∧ sQ l g ∈ GK (ϖ.field a) ∧ ∀ k : ℕ, ϖ.kummer (sQ l (g ^ k)) = ε ^ (c * k) := by
  first | exact @GlobalTheory.KummerMove.main | exact GlobalTheory.KummerMove.main | (intros; apply GlobalTheory.KummerMove.main <;> assumption)
