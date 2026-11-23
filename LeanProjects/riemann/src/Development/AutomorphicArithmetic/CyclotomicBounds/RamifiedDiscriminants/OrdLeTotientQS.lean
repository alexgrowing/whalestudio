import Mathlib
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.OrdLeQS

theorem UpperTheory.Ram.ord_le_totient_QS :
    ∀ {φ : Formalism.HC.Frame} (H : Formalism.HC.HostAx φ), φ.ord ≤ H.QS.totient ∧ 2 * φ.ord ≤ H.QS := by
  intro φ H
  obtain ⟨h1, h2, -⟩ := UpperTheory.KR.two_ord_le_QS H
  exact ⟨h1, h2⟩
