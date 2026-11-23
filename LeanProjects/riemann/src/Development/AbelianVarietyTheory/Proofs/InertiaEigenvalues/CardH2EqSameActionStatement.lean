import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardH2EqSameAction
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BijectiveOfRetract
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.ChartRestriction.T2 GlobalTheory.FunctorialityH2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_H2_eq_same_action : ∀ {R S : Type} [CommRing R] [CommRing S] {G : Type} [Group G] [TopologicalSpace G] {M : Type} [AddCommGroup M] [Module R M] [Module S M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [ContinuousConstSMul S M] (rho : Representation R G M) (rho' : Representation S G M), (∀ g m, rho g m = rho' g m) → Nat.card (H2 rho) = Nat.card (H2 rho') := by
  first | exact @GlobalTheory.H2CardScalars.card_H2_eq_of_same_action | exact GlobalTheory.H2CardScalars.card_H2_eq_of_same_action | (intros; apply GlobalTheory.H2CardScalars.card_H2_eq_of_same_action <;> assumption)
