import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoRows

noncomputable section

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TowU

variable {F : Type} [Field F] [NumberField F] {κ κ' : Type}

def dblAct (s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F)) (w : (κ ⊕ κ → AF F) × (κ ⊕ κ → AF F)) :
    (κ' ⊕ κ' → AF F) × (κ' ⊕ κ' → AF F) :=
  (Sum.elim (s (w.1 ∘ Sum.inl, w.2 ∘ Sum.inl)).1 (s (w.1 ∘ Sum.inr, -(w.2 ∘ Sum.inr))).1,
    Sum.elim (s (w.1 ∘ Sum.inl, w.2 ∘ Sum.inl)).2 (-(s (w.1 ∘ Sum.inr, -(w.2 ∘ Sum.inr))).2))

variable [Fintype κ] [Fintype κ']

structure IsOp (ψ : AddChar (AF F) ℂ) (s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F))
    (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) (S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) : Prop where
  pres : ∀ φ ∈ schA F κ, S φ ∈ schA F κ'
  pres' : ∀ φ ∈ schA F κ', S' φ ∈ schA F κ
  left : ∀ φ ∈ schA F κ, S' (S φ) = φ
  right : ∀ φ ∈ schA F κ', S (S' φ) = φ
  adm : ∀ l ∈ (adeleClass F).adm κ', l ∘ₗ S ∈ (adeleClass F).adm κ
  adm' : ∀ l ∈ (adeleClass F).adm κ, l ∘ₗ S' ∈ (adeleClass F).adm κ'
  Heisenberg₂ : ∀ w, ∀ φ ∈ schA F κ, S (schr ψ w φ) = schr ψ (s w) (S φ)
  theta : ∃ c : ℂ, c ≠ 0 ∧ ∀ φ ∈ schA F κ, thetaSum F (S φ) = c * thetaSum F φ
  norm : ∀ (μ : @Measure (κ → AF F) (borel _)) (μ' : @Measure (κ' → AF F) (borel _)),
    @Measure.IsAddHaarMeasure _ _ _ (borel _) μ → @Measure.IsAddHaarMeasure _ _ _ (borel _) μ' →
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ ∀ φ ∈ schA F κ, ∫⁻ x, ‖S φ x‖ₑ ^ 2 ∂μ' = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ

def IsOp2 (ψ : AddChar (AF F) ℂ) (s : (κ → AF F) × (κ → AF F) → (κ' → AF F) × (κ' → AF F))
    (S : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) (S' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)) : Prop :=
  IsOp ψ s S S' ∧ ∃ Sd Sd', IsOp ψ (dblAct s) Sd Sd' ∧
    ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ, Sd (boxFun φ₁ φ₂) = boxFun (S φ₁) (star (S (star φ₂)))

end GlobalTheory.TowU

end
