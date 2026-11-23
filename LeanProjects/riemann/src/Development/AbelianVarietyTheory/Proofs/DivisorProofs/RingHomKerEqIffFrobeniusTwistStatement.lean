import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomKerEqIffFrobeniusTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueEqZeroIffV
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringHom_ker_eq_iff_frobeniusTwist : ∀ (R k : Type) [CommRing R] [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (f : R →+* k) (h : ℕ), 0 < h → Nat.card (R ⧸ RingHom.ker f) = p ^ h → (∀ x : k, x ^ p ^ h = x → ∃ a, f a = x) ∧ ∃ F : ZMod h → (R →+* k), (∀ s a, F s a = f a ^ p ^ s.val) ∧ (∀ s a, F (s + 1) a = F s a ^ p) ∧ Function.Injective F ∧ ∀ g : R →+* k, RingHom.ker g = RingHom.ker f ↔ ∃ s, F s = g := by
  first | exact @GlobalTheory.FrobOrbit.ringHom_ker_eq_iff_frobenius_twist | exact GlobalTheory.FrobOrbit.ringHom_ker_eq_iff_frobenius_twist | (intros; apply GlobalTheory.FrobOrbit.ringHom_ker_eq_iff_frobenius_twist <;> assumption)
