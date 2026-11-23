import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionDegreeDvdCardInvariants
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_extension_degree_dvd_card_invariants : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (G : Type) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G], Function.Injective (algebraMap A B) → ∀ (k : Type) [Field k] [CharZero k] (ev : A →+* k), ∃ (K' : Type) (_ : Field K') (_ : Algebra k K') (β : B →+* K'), FiniteDimensional k K' ∧ Module.finrank k K' ∣ Nat.card G ∧ β.comp (algebraMap A B) = (algebraMap k K').comp ev := by
  first | exact @GlobalTheory.InvariantSpecialisation.exists_finite_extension_finrank_dvd | exact GlobalTheory.InvariantSpecialisation.exists_finite_extension_finrank_dvd | (intros; apply GlobalTheory.InvariantSpecialisation.exists_finite_extension_finrank_dvd <;> assumption)
