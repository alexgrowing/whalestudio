import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLocalMatrixDivisionPointQuotient
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsIotaAt
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_localMatrixDivisionPointQuotient : ∀ (E : Type) [Field E] [NumberField E] (w : IsDedekindDomain.HeightOneSpectrum (𝓞 E)) (N m n : ℕ), 0 < N → Nat.card (GlobalTheory.DivPtLocal.LocQ w N m n) = Nat.card (w.adicCompletionIntegers E ⧸ Ideal.span {((N : ℕ) : w.adicCompletionIntegers E)}) ^ (m * n) := by
  first | exact @GlobalTheory.DivPtLocal.Count.card_locQ | exact GlobalTheory.DivPtLocal.Count.card_locQ | (intros; apply GlobalTheory.DivPtLocal.Count.card_locQ <;> assumption)
