import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticGroupGeneratedByElementary
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymp
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplectic_group_generated_by_elementary : ∀ (K : Type) [Field K] [CharZero K] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Matrix (κ ⊕ κ) (κ ⊕ κ) K),
    GlobalTheory.SympChange.IsSymp G → G ∈ Submonoid.closure (GlobalTheory.SympChange.gens (F := K) (κ := κ)) := by
  first | exact @GlobalTheory.SympChangeGen.mem_closure_gens | exact GlobalTheory.SympChangeGen.mem_closure_gens | (intros; apply GlobalTheory.SympChangeGen.mem_closure_gens <;> assumption)
