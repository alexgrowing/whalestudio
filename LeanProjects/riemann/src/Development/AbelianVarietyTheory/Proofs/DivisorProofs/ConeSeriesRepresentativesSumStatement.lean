import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeSeriesRepresentativesSum
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
theorem _root_.GlobalTheory.T.cone_series_representatives_sum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (T : Set (UA σ J)), GlobalTheory.ConeSmallCT.IsReps T x →
    ∀ f : UA σ J → ℂ, (∀ p ∈ ratU σ J, GlobalTheory.ConeSmallSer.StabLn x p → ∀ h, f (p * h) = f h) →
    ∀ (S : Type) (φ : S → UA σ J), (∀ s, φ s ∈ ratU σ J) → (∀ s s', GlobalTheory.ConeSmallSer.StabLn x (φ s * (φ s')⁻¹) → s = s') →
    ∀ (g : UA σ J) (C : ℝ), Summable (fun t : T => ‖f (t.1 * g)‖) → ∑' t : T, ‖f (t.1 * g)‖ ≤ C →
      Summable (fun s => ‖f (φ s * g)‖) ∧ ∑' s, ‖f (φ s * g)‖ ≤ C := by
  first | exact @GlobalTheory.ConeSmallSerInt.summable_norm_le_of_distinct | exact GlobalTheory.ConeSmallSerInt.summable_norm_le_of_distinct | (intros; apply GlobalTheory.ConeSmallSerInt.summable_norm_le_of_distinct <;> assumption)
