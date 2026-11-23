import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfClosedMembershipLimit
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_closed_membership_limit : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (mem : (Fin d → Ainf l) → Prop), mem 0 → (∀ y z, mem y → mem z → mem (y + z)) → (∀ (c : bk.S) y, mem y → mem (fun a => bk.ev c * y a)) → (∀ y, mem (fun a => (l : Ainf l) * y a) → mem y) → (∀ y : ℕ → Fin d → Ainf l, (∀ n, mem (y n)) → (∀ n a, (l : Ainf l) ^ n ∣ y (n + 1) a - y n a) → ∀ z : Fin d → Ainf l, (∀ n a, (l : Ainf l) ^ n ∣ z a - y n a) → mem z) → ∀ (Y1 : Matrix (Fin d) (Fin d) (Ainf l)) (Y' : Matrix (Fin d) (Fin d) (WCb l)), (Y1.map (inclW l)).det ≠ 0 → IsUnit Y' → (∀ c : Fin d → bk.S, mem (Y1 *ᵥ fun a => bk.ev (c a))) → (∀ y, mem y → ∃ w : Fin d → WCb l, (∀ i, w i ∈ bk.OE) ∧ (fun a => inclW l (y a)) = Y' *ᵥ w) → ∃ Y : Matrix (Fin d) (Fin d) (Ainf l), IsUnit (Y.map (inclW l)) ∧ ∀ y, mem y ↔ ∃ c : Fin d → bk.S, y = Y *ᵥ fun a => bk.ev (c a) := by
  first | exact @GlobalTheory.BSP.saturated_module_free | exact GlobalTheory.BSP.saturated_module_free | (intros; apply GlobalTheory.BSP.saturated_module_free <;> assumption)
