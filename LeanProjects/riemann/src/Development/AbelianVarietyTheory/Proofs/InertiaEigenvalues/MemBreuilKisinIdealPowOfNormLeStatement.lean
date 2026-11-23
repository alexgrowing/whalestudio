import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBreuilKisinIdealPowOfNormLe
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_breuilKisinIdeal_pow_of_norm_le : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (A : Type) [CommRing A] (s : bk.S →+* A), (∀ x : A, (l : A) * x = 0 → x = 0) → (∀ (m : ℕ) (x y : A), (l : A) * x = s X ^ m * y → s X ^ m ∣ x) → ∀ (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ n : ℕ, ∃ r : ℝ, 0 < r ∧ ∀ x : A, ‖toDisc l (s X) ρ x‖ ≤ r → x ∈ (bk.J ^ n).map s := by
  first | exact @GlobalTheory.BSP.mem_J_pow_of_norm_le | exact GlobalTheory.BSP.mem_J_pow_of_norm_le | (intros; apply GlobalTheory.BSP.mem_J_pow_of_norm_le <;> assumption)
