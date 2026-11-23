import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DblOpOfConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeFixedAtOfSummands

noncomputable section

namespace GlobalTheory.ThK.LiftSemis

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LiftInv

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n : ℕ} {X : Spc F E n}

variable (σ X) in

def IsComplAt (v : Pl F) (A : Submodule ℂ (UA σ X.J → ℂ)) : Prop :=
  ∀ N : Submodule ℂ (UA σ X.J → ℂ), IsStableAt σ X v N → N ≤ A →
    ∃ C : Submodule ℂ (UA σ X.J → ℂ), IsStableAt σ X v C ∧ N ⊓ C = ⊥ ∧ N ⊔ C = A

variable (σ X) in

def fixedBy (K : Subgroup (UA σ X.J)) : Submodule ℂ (UA σ X.J → ℂ) where
  carrier := {x | ∀ k ∈ K, (fun g => x (g * k)) = x}
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

example (K : Subgroup (UA σ X.J)) (c : ℂ) : (fun _ => c) ∈ fixedBy σ X K := fun _ _ => rfl

end GlobalTheory.ThK.LiftSemis

end
