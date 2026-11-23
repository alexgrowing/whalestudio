import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalPartOperatorUnitaryCompatible
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_part_operator_unitary_compatible : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E) {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
    (M : Model σ X W) (M₁ : Model σ X₁ W₁), M.IsGood B.ψ → M₁.IsGood B.ψ →
    ∀ (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁) ei ev, IsLocPart M M₁ e ei ev →
    ∀ (v : Pl F) (T : Fn F n d → Fn F n d) (T₁ : Fn F n₁ d₁ → Fn F n₁ d₁) (c : ℂ),
      (∀ Φ ∈ schA F (Fin n × Fin d), e (T Φ) = c • T₁ (e Φ)) →
      ∀ φ φ₁ ψ₁, φ ∈ SB (Fin n × Fin d → Fv F v) → φ₁ ∈ SB (Fin n × Fin d → Fv F v) → ψ₁ ∈ SB (Fin n₁ × Fin d₁ → Fv F v) →
        Acts (evFin F v) T φ φ₁ → Acts (evFin F v) T₁ (ev v φ) ψ₁ → ev v φ₁ = c • ψ₁ := by
  first | exact @GlobalTheory.ThK.LemF.LocPartLaw.locPart_law | exact GlobalTheory.ThK.LemF.LocPartLaw.locPart_law | (intros; apply GlobalTheory.ThK.LemF.LocPartLaw.locPart_law <;> assumption)
