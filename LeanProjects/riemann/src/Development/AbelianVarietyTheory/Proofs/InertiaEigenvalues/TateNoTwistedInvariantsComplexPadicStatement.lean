import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateNoTwistedInvariantsComplexPadic
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tate_no_twisted_invariants_complexPadic : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (m : ℤ), m ≠ 0 → ∀ x : ℂ_[l], (∀ g : ↥(GK K), Per.σC (g : GQ l) x = ((((P.χQ (g : GQ l)) ^ m : ℚ_[l]ˣ) : ℚ_[l]) : ℂ_[l]) * x) → x = 0 := by
  first | exact @GlobalTheory.TateChiQ.tate_chiQ | exact GlobalTheory.TateChiQ.tate_chiQ | (intros; apply GlobalTheory.TateChiQ.tate_chiQ <;> assumption)
