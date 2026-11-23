import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuaSpanFiniteDimensionalDualPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOpMemDStep
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVacua_span_finiteDimensional_dualPair : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → FiniteDimensional ℂ (GlobalTheory.FockKFin.vacSp M B.emb) := by
  first | exact @GlobalTheory.FockKFin.vacSp_finiteDimensional | exact GlobalTheory.FockKFin.vacSp_finiteDimensional | (intros; apply GlobalTheory.FockKFin.vacSp_finiteDimensional <;> assumption)
