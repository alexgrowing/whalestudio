import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TracePowEqAlongLatticeTowerCover
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_pow_eq_along_latticeTowerCover : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] [TopologicalSpace Γ] (L₀ : FinExt l) (a : ℕ), 1 ≤ a → ∀ (r : Γ →* GL (Fin a) (Om l)) (Cl : Set (Γ →* GL (Fin a) (Om l))) (Cv : Cover L₀ r Cl) (σ : GQ l) (U : Matrix (Fin Cv.d) (Fin Cv.d) (ℂ_[l])) (U' : ∀ m, Matrix (Fin (Cv.tw.d' m)) (Fin (Cv.tw.d' m)) (ℂ_[l])) (Bd : ℝ) (S : ℕ → ℂ_[l]), S 0 = a → (∀ i j, ‖U i j‖ ≤ Bd) → (∀ m i j, ‖U' m i j‖ ≤ Bd) → (∀ n, ∃ m, n ≤ m ∧ ∀ i j, ‖(U * (Cv.tw.Pi m).map (fun x => algebraMap (Om l) ℂ_[l] (zOm l x)) - (Cv.tw.Pi m).map (fun x => algebraMap (Om l) ℂ_[l] (zOm l x)) * U' m) i j‖ ≤ Bd * ((l : ℝ) ^ n)⁻¹) → (∀ m k n, (∑ i, ((U' m ^ n) *ᵥ fun s => algebraMap (Om l) ℂ_[l] (zOm l ((Cv.lay m).e s))) i • ((Cv.lay m).b i k).map fun x => algebraMap (Om l) ℂ_[l] (σ x)).trace = S n) → ∀ n, (∑ i, ((U ^ n) *ᵥ fun s => algebraMap (Om l) ℂ_[l] (zOm l (Cv.e s))) i • (Cv.b i).map fun x => algebraMap (Om l) ℂ_[l] (σ x)).trace = S n := by
  first | exact @GlobalTheory.CoverTrace.trace_pow_eq | exact GlobalTheory.CoverTrace.trace_pow_eq | (intros; apply GlobalTheory.CoverTrace.trace_pow_eq; all_goals assumption)
