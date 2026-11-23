import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDeRhamFiltrationQuotientInvariants

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.TateFilQuotTied

theorem tied_tate_fil_quot : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied l P AI → ∀ K : FinExt l, Formalism.MainNotions.LocalSituation.TateFilteredInvariants (P.PD K) := by
  intro l _ P AI TT K LL _ _ _ O _ _ hO A hA a b z hz hg
  haveI := hO.2.1
  exact GlobalTheory.TateFilQuot.tied_invariant_mod l P AI TT K LL A.V A.ρ hA a b z hz hg

end GlobalTheory.TateFilQuotTied
