import Formalism.GradedWeylDivisibility.StatementA
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LBidetLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LBidetMinor

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem sum_initW_eq_shapeDeg {n K : ℕ} (sz : Fin K → ℕ) :
    (∑ k : Fin K, initW n (sz k)) = shapeDeg sz := by
  funext t
  rw [Finset.sum_apply]
  simp only [initW, shapeDeg, Finset.card_filter]

theorem bideterminantMem : BideterminantMem := by
  intro R _ r n K sz hsz I
  exact dualWeyl_of_eq
    (dualWeyl_prod Finset.univ (fun k => initW n (sz k))
      (fun k => initMinor R (I k) (hsz k))
      (fun k _ => initMinor_mem (I k) (hsz k)))
    (sum_initW_eq_shapeDeg sz)

end Formalism.GradedWeylDivisibility
