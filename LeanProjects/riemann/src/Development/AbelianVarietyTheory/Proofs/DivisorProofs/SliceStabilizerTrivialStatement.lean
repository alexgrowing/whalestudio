import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SliceStabilizerTrivial
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmAOneApply
open Matrix MeasureTheory ValuativeRel GlobalTheory.SplitFlip GlobalTheory.SmGL GlobalTheory.WeilM GlobalTheory.RankFibre GlobalTheory.SplitWeil GlobalTheory.RankFibreKer

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slice_stabilizer_trivial : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a d : ℕ) (Z : Matrix (Fin a) (Fin d) k) (g : GL (Fin a) k), Z ∈ slice k a d → g.val * Z ∈ slice k a d → g = 1 := by
  first | exact @GlobalTheory.RankFibreKer.eq_one_of_mem_slice_of_mul_mem_slice | exact GlobalTheory.RankFibreKer.eq_one_of_mem_slice_of_mul_mem_slice | (intros; apply GlobalTheory.RankFibreKer.eq_one_of_mem_slice_of_mul_mem_slice <;> assumption)
