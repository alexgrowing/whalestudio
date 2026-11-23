import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev

noncomputable section

namespace GlobalTheory.ThK.DescB.PlaneTwo

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n n₁ n₂ : ℕ}

def xTwo (H₁ : Plane E n n₁) (H₂ : Plane E n₁ n₂) : Fin n → E := H₁.ι *ᵥ H₂.x

def yTwo (H₁ : Plane E n n₁) (H₂ : Plane E n₁ n₂) : Fin n → E := H₁.ι *ᵥ H₂.y

def ιTwo (H₁ : Plane E n n₁) (H₂ : Plane E n₁ n₂) : Matrix (Fin n) (Fin n₂) E := H₁.ι * H₂.ι

variable (σ) in

def unipTwo (Y : Spc F E n) (H₁ : Plane E n n₁) (H₂ : Plane E n₁ n₂) : Subgroup (UA σ Y.J) :=
  Subgroup.closure {u | mat u *ᵥ incV F H₁.x = incV F H₁.x ∧ mat u *ᵥ incV F (xTwo H₁ H₂) = incV F (xTwo H₁ H₂) ∧
    ∀ z, ∃ a b : AE F E, mat u *ᵥ (incM F (ιTwo H₁ H₂) *ᵥ z) =
      incM F (ιTwo H₁ H₂) *ᵥ z + a • incV F H₁.x + b • incV F (xTwo H₁ H₂)}

def IsCTTwo {Y : Spc F E n} (H₁ : Plane E n n₁) (H₂ : Plane E n₁ n₂) (f c : UA σ Y.J → ℂ) : Prop :=
  ∀ (μ : Measure (unipTwo σ Y H₁ H₂)) (𝓕 : Set (unipTwo σ Y H₁ H₂)), μ.IsHaarMeasure →
    IsFundamentalDomain ((ratU σ Y.J).subgroupOf (unipTwo σ Y H₁ H₂)) 𝓕 μ → μ 𝓕 = 1 →
    ∀ h, c h = ∫ u in 𝓕, f (u.1 * h) ∂μ

def IsCentreTwo {Y : Spc F E n} (H₁ : Plane E n n₁) (H₂ : Plane E n₁ n₂) (t : (AE F E)ˣ) (h : UA σ Y.J) : Prop :=
  mat h *ᵥ incV F H₁.x = t.1 • incV F H₁.x ∧ mat h *ᵥ incV F (xTwo H₁ H₂) = t.1 • incV F (xTwo H₁ H₂) ∧
    mat h *ᵥ incV F H₁.y = cA σ (t⁻¹).1 • incV F H₁.y ∧
    mat h *ᵥ incV F (yTwo H₁ H₂) = cA σ (t⁻¹).1 • incV F (yTwo H₁ H₂) ∧
    mat h * incM F (ιTwo H₁ H₂) = incM F (ιTwo H₁ H₂)

def HasCentreLaw {Y : Spc F E n} (H₁ : Plane E n n₁) (H₂ : Plane E n₁ n₂) (χ χ' : Chr F E) (w : ℝ) (T : UA σ Y.J → ℂ) :
    Prop :=
  ∀ t m, IsCentreTwo H₁ H₂ t m → ∀ h, T (m * h) = (χ t : ℂ) * (χ' t : ℂ) * (((absE F E t : ℝ) ^ w : ℝ) : ℂ) * T h

end GlobalTheory.ThK.DescB.PlaneTwo

end
