import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeSeriesLocallyUniform
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCtIntSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisjointLineMid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeOfReNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsShear
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallMidJB

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_series_locally_uniform : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d d₁ : ℕ)
    (W : Spc F E d) (H' : Plane E d d₁) (R : ℝ≥0), (∀ u ∈ unip σ W H', ∃ γ ∈ ratU σ W.J ⊓ unip σ W H', ht (γ * u) ≤ R) →
    ∀ T : Set (UA σ W.J), GlobalTheory.ConeSmallCT.IsReps T H'.x → ∀ f : UA σ W.J → ℂ,
    (∀ p ∈ ratU σ W.J, GlobalTheory.ConeSmallSer.StabLn H'.x p → ∀ h, f (p * h) = f h) → GlobalTheory.ConeSmallCT.LocUnifSum f T →
    ∀ h, ∃ C : ℝ, ∀ u ∈ unip σ W H', Summable (fun t : T => ‖f (t.1 * (u * h))‖) ∧ ∑' t : T, ‖f (t.1 * (u * h))‖ ≤ C := by
  first | exact @GlobalTheory.ConeSmallSumBd.sum_bounded | exact GlobalTheory.ConeSmallSumBd.sum_bounded | (intros; apply GlobalTheory.ConeSmallSumBd.sum_bounded <;> assumption)
