import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepSliceFiniteOp
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvFinMkPt

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.FinComm GlobalTheory.VacLine

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_rep_slice_finite_op : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (v : Pl F)
    (w : Matrix (Fin n) (Fin d) (AE F E)), At (evFin F v) w →
    ∀ (Φ : (Fin n × Fin d → AF F) → ℂ) (x : Fin n × Fin d → mixedEmbedding.mixedSpace F),
      slice (M.co.rho ψ w Φ) x = finOp ψ v (locPt v (M.co.e w)) (slice Φ x) := by
  first | exact @GlobalTheory.VacLine.RhoSlice.rho_slice | exact GlobalTheory.VacLine.RhoSlice.rho_slice | (intros; apply GlobalTheory.VacLine.RhoSlice.rho_slice <;> assumption)
