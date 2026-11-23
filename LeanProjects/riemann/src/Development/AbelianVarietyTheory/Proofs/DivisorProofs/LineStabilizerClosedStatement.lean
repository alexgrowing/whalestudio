import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineStabilizerClosed
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_stabilizer_closed : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n n₁ : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (ι : Matrix (Fin n) (Fin n₁) E), x ≠ 0 →
    IsClosed (GlobalTheory.IwLine.lineStab σ J x : Set (UA σ J)) ∧
    IsClosed {u : UA σ J | mat u *ᵥ incV F x = incV F x ∧
      ∀ z, ∃ a : AE F E, mat u *ᵥ (incM F ι *ᵥ z) = incM F ι *ᵥ z + a • incV F x} := by
  first | exact @GlobalTheory.LineStabClosed.isClosed_lineStab_unip | exact GlobalTheory.LineStabClosed.isClosed_lineStab_unip | (intros; apply GlobalTheory.LineStabClosed.isClosed_lineStab_unip <;> assumption)
