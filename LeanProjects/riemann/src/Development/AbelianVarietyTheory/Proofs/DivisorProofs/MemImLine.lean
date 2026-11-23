import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoC

open scoped TensorProduct Matrix
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.UnipConj

open GlobalTheory.ThK.UnipDom

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def imLine (σ : E →ₐ[F] E) : AddSubgroup (AE F E) where
  carrier := {t | t + cA σ t = 0}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, map_add] at *
    calc a + b + (cA σ a + cA σ b) = (a + cA σ a) + (b + cA σ b) := by abel
      _ = 0 := by rw [ha, hb, add_zero]
  neg_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq, map_neg] at *
    rw [← neg_add, ha, neg_zero]

theorem mem_imLine {σ : E →ₐ[F] E} {t : AE F E} : t ∈ imLine σ ↔ t + cA σ t = 0 := Iff.rfl

def betaOf (σ : E →ₐ[F] E) {b : ℕ} (J₁ : Matrix (Fin b) (Fin b) E) (a : Fin b → AE F E) : Fin b → AE F E :=
  fun i => -cA σ ((incM F J₁⁻¹ *ᵥ a) i)

def coT (σ : E →ₐ[F] E) {d d₁ : ℕ} (J : Matrix (Fin d) (Fin d) E) (H : Plane E d d₁) (g : UA σ J) : AE F E :=
  coC σ J H g - cA σ (coC σ J H g)

end GlobalTheory.UnipConj
