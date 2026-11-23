import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalNormInfinitePlaceBound
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
theorem _root_.GlobalTheory.T.local_norm_infinite_place_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Type) [Fintype J] (w : InfinitePlace F) (e : EmbOver E w) (u : J → E) (δ : (w.Completion ⊗[F] E)ˣ) (z : J → w.Completion ⊗[F] E) (c : ℝ≥0),
    (∀ f, z f = ((1 : w.Completion) ⊗ₜ[F] u f) * δ.1) → (∀ f, ‖infEmb e (z f)‖₊ ≤ c) →
    GlobalTheory.Doubling.absEw F E w δ * locInf w u ≤ c ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.absEw_mul_locInf_le | exact GlobalTheory.CompanionTheory.GodementH.absEw_mul_locInf_le | (intros; apply GlobalTheory.CompanionTheory.GodementH.absEw_mul_locInf_le <;> assumption)
