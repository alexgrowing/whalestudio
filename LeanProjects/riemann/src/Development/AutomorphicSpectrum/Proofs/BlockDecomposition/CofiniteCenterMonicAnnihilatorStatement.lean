import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CofiniteCenterMonicAnnihilator
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapS
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl GlobalTheory.CompanionTheory.CTFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cofinite_center_monic_annihilator : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ) (J : Set (Module.End ℂ (Sm E n))), Cofin J → ∀ z ∈ Zalg E n, ∃ p : Polynomial ℂ, p.Monic ∧ ∀ φ : Sm E n, (∀ j ∈ J, j φ = 0) → Polynomial.aeval z p φ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.CTFin.cofin_monic_on_killed | exact GlobalTheory.CompanionTheory.CTFin.cofin_monic_on_killed | (intros; apply GlobalTheory.CompanionTheory.CTFin.cofin_monic_on_killed <;> assumption)
