import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1BallCocycleLogCyclotomic
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_eq_log_cyclotomic_smul_add_coboundary : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ s : ℕ, Lev l s → (∀ c : GQ l → PadicComplex l, CocOn (Gj K s) (fun g y => act g y) {y | ‖y‖ ≤ 1} c → ∃ α ∈ inC (Ks K s), ‖α‖ ≤ (l : ℝ) ^ (1 + s) ∧ ∃ b : PadicComplex l, ∀ σ ∈ Gj K s, c σ = algebraMap ℚ_[l] (PadicComplex l) (logZl l (χ σ : ℚ_[l])) * α + (act σ b - b)) ∧ ∀ α ∈ inC (Ks K s), ∀ b : PadicComplex l, (∀ σ ∈ Gj K s, algebraMap ℚ_[l] (PadicComplex l) (logZl l (χ σ : ℚ_[l])) * α = act σ b - b) → α = 0 := by
  first | exact @GlobalTheory.Cyc.LogClass.image_H1_logChi | exact GlobalTheory.Cyc.LogClass.image_H1_logChi | (intros; apply GlobalTheory.Cyc.LogClass.image_H1_logChi <;> assumption)
