import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLagrAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory
open scoped TensorProduct Matrix GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.InertLagChar

variable {F : Type} [Field F] [NumberField F] {v : Pl F} {κ : Type} [Fintype κ]

def diagW (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _)) (Φ : (κ ⊕ κ → Fv F v) → ℂ)
    (w : (κ → Fv F v) × (κ → Fv F v)) : ℂ :=
  ∫ x, schr ψ (Sum.elim w.1 0, Sum.elim w.2 0) Φ (Sum.elim x x) ∂μ

def lagInt (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _)) {N : ℕ} (ν : @Measure (Fin N → Fv F v) (borel _))
    (j : (Fin N → Fv F v) →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v)) (Φ : (κ ⊕ κ → Fv F v) → ℂ) : ℂ :=
  ∫ y, diagW ψ μ Φ (j y) ∂ν

open NumberField IsDedekindDomain MeasureTheory in
open scoped TensorProduct Matrix in
variable {F : Type} [Field F] [NumberField F] {v : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} {κ : Type} [Fintype κ] in

theorem _root_.GlobalTheory.InertLagChar.diagW_zero (ψ : AddChar (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ℂ)
    (μ : @Measure (κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (borel _)) (Φ : (κ ⊕ κ → _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) :
    _root_.GlobalTheory.InertLagChar.diagW ψ μ Φ 0 = ∫ x, Φ (Sum.elim x x) ∂μ := by
  unfold _root_.GlobalTheory.InertLagChar.diagW _root_.GlobalTheory.WeilM.schr
  simp

end GlobalTheory.InertLagChar
end
