import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DOpMemDStep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinPartNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU

noncomputable section

namespace GlobalTheory.ArchPureAct

theorem acts_pure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (ψ : AddChar (AF F) ℂ) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (om : Rep σ X W), M.IsGood ψ →
    ∀ (x : UA σ X.J × UA σ W.J) (A : SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d)),
    (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om x) ⇑f ⇑(A f)) →
    ∀ (f : SInf F (Fin n × Fin d)) (φ : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ), (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
      (∀ᶠ v in Filter.cofinite, φ v = M.vac v) → om x (pure f φ) = pure (A f) φ := by
  intro F E _ _ _ _ _ σ ψ n d X W M om hM x A hA f φ hSB hcof
  have hstd : ∀ᶠ v in Filter.cofinite,
      φ v = Set.indicator {y | ∀ i, y i ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v} 1 :=
    (hcof.and hM.std).mono fun v hv => hv.1.trans hv.2
  have hrest : Rest (evI F) (⇑f) (GlobalTheory.EvZeroInf.finPart φ) :=
    ⟨fun y z hz => GlobalTheory.EvZeroInf.finPart_add φ y z hz, GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩
  exact hA f _ hrest

end GlobalTheory.ArchPureAct

end
