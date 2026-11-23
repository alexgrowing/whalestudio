import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CofiniteOfCapelliMonic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapS
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cofinite_of_capelli_monic : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (J : Set (Module.End ℂ (Sm E n))), J ⊆ Zalg E n → (∀ (τ : E →+* ℂ) (u : ℂ), ∃ q : Polynomial ℂ, q.Monic ∧ Polynomial.aeval (cap (a := n) τ u) q ∈ J) → Cofin J := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.MonicCofin.cofin_of_monic | exact GlobalTheory.CompanionTheory.CTFin.MonicCofin.cofin_of_monic | (intros; apply GlobalTheory.CompanionTheory.CTFin.MonicCofin.cofin_of_monic <;> assumption)
