import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.DblEval

section Blocks

variable {A : Type} {κ κ₁ κ' κ₁' : Type}

def partL (T : ((κ → A) → ℂ) → (κ₁ → A) → ℂ) (Φ : (κ ⊕ κ' → A) → ℂ) : (κ₁ ⊕ κ' → A) → ℂ :=
  fun y => T (fun x => Φ (Sum.elim x (y ∘ Sum.inr))) (y ∘ Sum.inl)

def partR (T : ((κ' → A) → ℂ) → (κ₁' → A) → ℂ) (Φ : (κ ⊕ κ' → A) → ℂ) : (κ ⊕ κ₁' → A) → ℂ :=
  fun y => T (fun x => Φ (Sum.elim (y ∘ Sum.inl) x)) (y ∘ Sum.inr)

def partLₗ (e : ((κ → A) → ℂ) →ₗ[ℂ] (κ₁ → A) → ℂ) : ((κ ⊕ κ' → A) → ℂ) →ₗ[ℂ] (κ₁ ⊕ κ' → A) → ℂ where
  toFun := partL e
  map_add' Φ Ψ := funext fun y => by
    show e ((fun x => Φ _) + fun x => Ψ _) _ = _
    rw [map_add]; rfl
  map_smul' c Φ := funext fun y => by
    show e (c • fun x => Φ _) _ = _
    rw [map_smul]; rfl

def partRₗ (e : ((κ' → A) → ℂ) →ₗ[ℂ] (κ₁' → A) → ℂ) : ((κ ⊕ κ' → A) → ℂ) →ₗ[ℂ] (κ ⊕ κ₁' → A) → ℂ where
  toFun := partR e
  map_add' Φ Ψ := funext fun y => by
    show e ((fun x => Φ _) + fun x => Ψ _) _ = _
    rw [map_add]; rfl
  map_smul' c Φ := funext fun y => by
    show e (c • fun x => Φ _) _ = _
    rw [map_smul]; rfl

@[simp] theorem partLₗ_apply (e : ((κ → A) → ℂ) →ₗ[ℂ] (κ₁ → A) → ℂ) (Φ : (κ ⊕ κ' → A) → ℂ) :
    partLₗ e Φ = partL e Φ := rfl

@[simp] theorem partRₗ_apply (e : ((κ' → A) → ℂ) →ₗ[ℂ] (κ₁' → A) → ℂ) (Φ : (κ ⊕ κ' → A) → ℂ) :
    partRₗ e Φ = partR e Φ := rfl

end Blocks

def conjLin {X Y : Type} (e : (X → ℂ) →ₗ[ℂ] (Y → ℂ)) : (X → ℂ) →ₗ[ℂ] (Y → ℂ) where
  toFun φ y := starRingEnd ℂ (e (fun x => starRingEnd ℂ (φ x)) y)
  map_add' φ ψ := funext fun y => by
    have h : (fun x => starRingEnd ℂ (φ x + ψ x)) = (fun x => starRingEnd ℂ (φ x)) + fun x => starRingEnd ℂ (ψ x) :=
      funext fun x => map_add _ _ _
    simp only [Pi.add_apply]
    rw [h, map_add, Pi.add_apply, map_add]
  map_smul' c φ := funext fun y => by
    have h : (fun x => starRingEnd ℂ (c * φ x)) = starRingEnd ℂ c • fun x => starRingEnd ℂ (φ x) :=
      funext fun x => by simp
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [h, map_smul, Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_conj]

theorem conjLin_apply {X Y : Type} (e : (X → ℂ) →ₗ[ℂ] (Y → ℂ)) (φ : X → ℂ) (y : Y) :
    conjLin e φ y = starRingEnd ℂ (e (fun x => starRingEnd ℂ (φ x)) y) := rfl

section Loc

variable (F : Type) [Field F] [NumberField F]

def stdInd (κ : Type) (v : Pl F) : (κ → Fv F v) → ℂ := Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1

variable {F}

def IsLocOp {κ κ₁ : Type} [Fintype κ] [Fintype κ₁] (e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ₁ → AF F) → ℂ) : Prop :=
  ∃ (ei : SInf F κ →L[ℂ] SInf F κ₁) (ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ₁ → Fv F v) → ℂ),
    (∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ ∈ SB (κ₁ → Fv F v)) ∧
    (∀ᶠ v in cofinite, ev v (stdInd F κ v) = stdInd F κ₁ v) ∧
    ∀ (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) →
      (∀ᶠ v in cofinite, φ v = stdInd F κ v) → e (pure f φ) = pure (ei f) fun v => ev v (φ v)

end Loc

end GlobalTheory.DblEval

end
