import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitUnitaryIdempotentTendsto
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseAdeleExtInfiniteFinite

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_unitary_idempotent_tendsto : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (g : UA σ J), At (fun u : AF F => u.2) (mat g - 1) → Filter.Tendsto (fun S : Finset (Pl F) => GlobalTheory.TailFix.splU (GlobalTheory.TailFix.idem S) (GlobalTheory.TailFix.idem_mul_self S) g) Filter.atTop (𝓝 g) := by
  first | exact @GlobalTheory.TailFix.tendsto_splU | exact GlobalTheory.TailFix.tendsto_splU | (intros; apply GlobalTheory.TailFix.tendsto_splU <;> assumption)
