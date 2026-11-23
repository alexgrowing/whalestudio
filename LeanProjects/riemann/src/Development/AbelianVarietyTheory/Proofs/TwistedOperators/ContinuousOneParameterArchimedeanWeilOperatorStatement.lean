import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousOneParameterArchimedeanWeilOperator
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchActOne

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_oneParameter_archimedean_weilOperator : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    M.IsWeil ψ χX χW om → (∀ h ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, h)) ⇑f ⇑f₁) → ∀ γ ∈ Lines σ W,
    ∀ (f : SInf F (Fin n × Fin d)) (x : Fin n × Fin d → mixedEmbedding.mixedSpace F),
      Continuous fun t : ℝ => archOp om (γ (Multiplicative.ofAdd t)) f x := by
  first | exact @GlobalTheory.ArchLine.archOp_apply_continuous | exact GlobalTheory.ArchLine.archOp_apply_continuous | (intros; apply GlobalTheory.ArchLine.archOp_apply_continuous <;> assumption)
