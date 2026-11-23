import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanMinorHeightBound
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
theorem _root_.GlobalTheory.T.archimedean_minor_height_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (w : InfinitePlace F) (τ : EmbOver E w) (X : GL ι (AE F E)) (κ : Matrix ι ι (AE F E)),
    κ.map (piInf τ) * (κ.map (piInf τ))ᴴ = 1 → ∀ f e : Fin n → ι,
    ‖piInf τ ((X.1 * κ).submatrix f e).det‖₊ ≤ (n.factorial : ℝ≥0) * htInf F w (Formalism.UG.bc (compInf F E w) X) ^ n := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.MinInf.minor_le_htInf | exact GlobalTheory.CompanionTheory.GodementH.MinInf.minor_le_htInf | (intros; apply GlobalTheory.CompanionTheory.GodementH.MinInf.minor_le_htInf <;> assumption)
