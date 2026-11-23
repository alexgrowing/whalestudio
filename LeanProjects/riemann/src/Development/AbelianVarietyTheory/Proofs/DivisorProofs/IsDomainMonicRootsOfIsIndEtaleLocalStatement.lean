import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDomainMonicRootsOfIsIndEtaleLocal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isDomain_monicRoots_of_isIndEtale_local : ∀ (T O : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O], IndEt T O → (∀ (E : Type) [CommRing E] [Algebra T E] [Algebra.Etale T E] (P : Ideal E) [P.IsPrime], IsDomain (Localization.AtPrime P) ∧ AIC (Localization.AtPrime P)) → IsDomain O ∧ AIC O := by
  first | (exact @GlobalTheory.LocalIndEtAIC.isDomain_aic_of_indEt) | (exact GlobalTheory.LocalIndEtAIC.isDomain_aic_of_indEt) | (intros; apply GlobalTheory.LocalIndEtAIC.isDomain_aic_of_indEt  <;> assumption)
