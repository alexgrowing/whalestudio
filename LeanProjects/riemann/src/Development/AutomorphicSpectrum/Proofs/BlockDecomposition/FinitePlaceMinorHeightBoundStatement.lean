import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePlaceMinorHeightBound
import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EmbBar
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_place_minor_height_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (v : Pl F) (X : GL ι (AE F E)) (κ : Matrix ι ι (AE F E)),
    (∀ i j, absFin F v (compFin F E v (κ i j)) ≤ 1) → ∀ f e : Fin n → ι,
    absFin F v (compFin F E v ((X.1 * κ).submatrix f e).det) ≤ htFin F v (Formalism.UG.bc (compFin F E v) X) ^ n := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.absFin_minor_mul_le | exact GlobalTheory.CompanionTheory.GodementH.absFin_minor_mul_le | (intros; apply GlobalTheory.CompanionTheory.GodementH.absFin_minor_mul_le <;> assumption)
