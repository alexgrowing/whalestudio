import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorIdeleConstant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_operator_idele_locallyConstant : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (H : Plane E n n₁)
    (H' : Plane E d d₁), Continuous B.ψ → ∀ (v : Pl F), ∀ ψ ∈ SB (Fin n × Fin d → Fv F v),
    ∃ g : (Fv F v ⊗[F] E) → (Fin n × Fin d → Fv F v) → ℂ, IsLocallyConstant g ∧
      ∀ l ∈ idelesAt E (evFin F v), locOp v (M.co.rho B.ψ (partFin v (shiftB σ H H' l))) ψ =
        g ((GlobalTheory.Doubling.unitFin F E v l : (Fv F v ⊗[F] E)ˣ) : Fv F v ⊗[F] E) := by
  first | exact @GlobalTheory.SchrLocConst.shiftB_locOp_locallyConstant | exact GlobalTheory.SchrLocConst.shiftB_locOp_locallyConstant | (intros; apply GlobalTheory.SchrLocConst.shiftB_locOp_locallyConstant <;> assumption)
