import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentStabilizerRelativelyCompact
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeEvFun
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsPowApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingLocalMeasurable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLatticeIsClosed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarRightInvariantCompact
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
open GlobalTheory.ThK.LemF.QuotInv

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_stabilizer_relatively_compact : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (Y : Spc F E n) (v : Pl F) (x : Fin n → E) (q : stabAt σ Y (evFin F v) x), (mat q.1.1 - 1) ^ 3 = 0 →
    ∃ P : Set (Matrix (Fin n) (Fin n) (AE F E)), IsCompact P ∧
      ∀ g ∈ Subgroup.zpowers q, mat g.1.1 ∈ P ∧ mat g.1.1⁻¹ ∈ P := by
  first | exact @GlobalTheory.ThK.LemF.QuotInv.PowSet.exists_compact_zpowers | exact GlobalTheory.ThK.LemF.QuotInv.PowSet.exists_compact_zpowers | (intros; apply GlobalTheory.ThK.LemF.QuotInv.PowSet.exists_compact_zpowers <;> assumption)
