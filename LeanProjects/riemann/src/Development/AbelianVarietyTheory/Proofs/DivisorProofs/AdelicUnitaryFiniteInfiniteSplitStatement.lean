import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicUnitaryFiniteInfiniteSplit
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_unitary_finite_infinite_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (W : Spc F E n) (g : UA σ W.J), ∃ gi ∈ UAt σ W (evI F), ∃ gf ∈ UAt σ W (fun u : AF F => u.2), g = gi * gf := by
  first | exact @GlobalTheory.ArchFinSplit.split_arch_fin | exact GlobalTheory.ArchFinSplit.split_arch_fin | (intros; apply GlobalTheory.ArchFinSplit.split_arch_fin <;> assumption)
