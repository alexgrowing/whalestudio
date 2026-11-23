import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumRankinSelbergSchurTermFinsuppEulerProduct
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
open MeasureTheory
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_rankinSelbergSchurTerm_finsupp_eulerProduct : ∀ {I : Type} (q : I → ℕ) {n : ℕ} (α β : I → Fin n → ℂˣ) (x : ℝ), 1 < x → (∀ i, 2 ≤ q i) →
    GlobalTheory.RSPole.eulD q (fun i j => (α i j : ℂ)) x ≠ ⊤ → GlobalTheory.RSPole.eulD q (fun i j => (β i j : ℂ)) x ≠ ⊤ →
    HasSum (fun l : I →₀ (Fin n → ℤ) => l.prod fun i v => GlobalTheory.ZEul.rsTerm (q i) (fun j => (α i j : ℂ)) (fun j => (β i j : ℂ)) x v)
      (∏' i, GlobalTheory.JSW.locL (q i) (Finset.univ.val.map (α i)) ((Finset.univ.val.map (β i)).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) := by
  first | exact @GlobalTheory.ZEul.hasSum_rsTerm_finsupp | exact GlobalTheory.ZEul.hasSum_rsTerm_finsupp | (intros; apply GlobalTheory.ZEul.hasSum_rsTerm_finsupp <;> assumption)
