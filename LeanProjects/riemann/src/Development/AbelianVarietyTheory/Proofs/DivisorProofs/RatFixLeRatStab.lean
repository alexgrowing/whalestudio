import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

noncomputable section

namespace GlobalTheory.ConeSmallClaim

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable (σ) in

def ratFix {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) : Subgroup (UA σ J) where
  carrier := {γ | γ ∈ ratU σ J ∧ mat γ *ᵥ incV F x = incV F x}
  mul_mem' := by
    rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
    refine ⟨mul_mem hg hh, ?_⟩
    have : mat (g * h) = mat g * mat h := rfl
    rw [this, ← Matrix.mulVec_mulVec, hh', hg']
  one_mem' := ⟨one_mem _, by simp [mat]⟩
  inv_mem' := by
    rintro g ⟨hg, hg'⟩
    refine ⟨inv_mem hg, ?_⟩
    have h1 : mat g⁻¹ * mat g = 1 := by simp [mat]
    calc mat g⁻¹ *ᵥ incV F x = mat g⁻¹ *ᵥ (mat g *ᵥ incV F x) := by rw [hg']
      _ = incV F x := by rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

theorem ratFix_le_ratStab {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x : Fin n → E) :
    ratFix σ J x ≤ ratStab σ J x := fun γ ⟨hγ, hx⟩ => ⟨hγ, 1, by rw [hx, Units.val_one, one_smul]⟩

def NonProp {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (R : Set (IsoV σ J)) : Prop :=
  ∀ w ∈ R, ∀ w' ∈ R, ∀ ξ : Eˣ, w.1 = (ξ : E) • w'.1 → w = w'

example {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (w : IsoV σ J) : NonProp ({w} : Set (IsoV σ J)) := by
  rintro a rfl b rfl _ _; rfl

end GlobalTheory.ConeSmallClaim

end
