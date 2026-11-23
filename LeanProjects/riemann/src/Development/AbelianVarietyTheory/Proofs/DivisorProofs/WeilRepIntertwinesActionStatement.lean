import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepIntertwinesAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOpMemDStep
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_rep_intertwines_action : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (ψ : AddChar (AF F) ℂ) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (om : Rep σ X W), M.IsGood ψ →
    ∀ (x : UA σ X.J × UA σ W.J) (A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)),
    (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om x) ⇑f ⇑(A f)) →
    ∀ (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ), (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
      (∀ᶠ v in Filter.cofinite, φ v = M.vac v) → om x (pure f φ) = pure (A f) φ := by
  first | exact @GlobalTheory.ArchPureAct.acts_pure | exact GlobalTheory.ArchPureAct.acts_pure | (intros; apply GlobalTheory.ArchPureAct.acts_pure <;> assumption)
