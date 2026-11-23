import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DblOpOfConst

noncomputable section

namespace GlobalTheory.ThK.LiftInv

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

variable (σ X) in

def IsStableAt (v : Pl F) (N : Submodule ℂ (UA σ X.J → ℂ)) : Prop :=
  ∀ k ∈ UAt σ X (evFin F v), ∀ x ∈ N, (fun g => x (g * k)) ∈ N

variable (σ X) in

def IsSimpleAt (v : Pl F) (N : Submodule ℂ (UA σ X.J → ℂ)) : Prop :=
  N ≠ ⊥ ∧ ∀ N' : Submodule ℂ (UA σ X.J → ℂ), IsStableAt σ X v N' → N' ≤ N → N' = ⊥ ∨ N' = N

variable (σ X) in

def IsSummandAt (v : Pl F) (S N : Submodule ℂ (UA σ X.J → ℂ)) : Prop :=
  N ≤ S ∧ IsStableAt σ X v N ∧ ∃ C : Submodule ℂ (UA σ X.J → ℂ), IsStableAt σ X v C ∧ N ⊓ C = ⊥ ∧ N ⊔ C = S

def liftSpan (om : Rep σ X W) (μ : Measure (UA σ W.J)) (𝓕 : Set (UA σ W.J)) (D : Set ((Fin n × Fin d → AF F) → ℂ))
    (fs : Set (UA σ W.J → ℂ)) : Submodule ℂ (UA σ X.J → ℂ) :=
  Submodule.span ℂ {x | ∃ Φ ∈ D, ∃ f ∈ fs, x = GlobalTheory.ThK.DoublingLifts.liftW om μ 𝓕 Φ f}

variable (σ X) in

def fixedAt (v : Pl F) : Submodule ℂ (UA σ X.J → ℂ) where
  carrier := {x | ∀ k ∈ UAt σ X (evFin F v), (fun g => x (g * k)) = x}
  add_mem' := by
    intro x y hx hy k hk
    funext g
    simp only [Pi.add_apply]
    rw [congrFun (hx k hk) g, congrFun (hy k hk) g]
  zero_mem' := by
    intro k _
    rfl
  smul_mem' := by
    intro c x hx k hk
    funext g
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [congrFun (hx k hk) g]

end GlobalTheory.ThK.LiftInv

end
