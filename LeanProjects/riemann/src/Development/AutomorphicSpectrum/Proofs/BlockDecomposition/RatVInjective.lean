import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.SiegelPar
import GroundTheory.AutomorphicForms.ReductionHeight

set_option linter.unusedSectionVars false

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.RedCov

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}

variable (F) in

def ratV (z : Fin n → E) : Fin n → AF F ⊗[F] E := fun i => inclR (F := F) (AF F) (z i)

def hv (ξ : Fin n → AF F ⊗[F] E) : ℝ :=
  GroundTheory.Automorphic.Reduction.adelicNorm
    (fun p : Fin (Fintype.card (Fin n × Fin (Module.finrank F E))) =>
      (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).repr
        (ξ ((Fintype.equivFin (Fin n × Fin (Module.finrank F E))).symm p).1)
        ((Fintype.equivFin (Fin n × Fin (Module.finrank F E))).symm p).2)

def hgt (g : GAd σ J) (v : Fin n → E) : ℝ := hv ((matHom _ σ J g⁻¹).1 *ᵥ ratV F v)

def Sends (γ : GAd σ J) (u v : Fin n → E) : Prop := (matHom _ σ J γ).1 *ᵥ ratV F u = ratV F v

def NearMin (g : GAd σ J) (v : Fin n → E) : Prop :=
  v ≠ 0 ∧ hE σ J v v = 0 ∧ ∀ u : Fin n → E, u ≠ 0 → hE σ J u u = 0 → hgt σ J g v ≤ 2 * hgt σ J g u

def HasRed (X Y : Matrix (Fin n) (Fin r) E) : Prop :=
  ∀ a, IsTorus σ J X Y a → ∃ (C : Set (GAd σ J)) (c : ℝ), IsCompact C ∧ 0 < c ∧
    ∀ g, ∃ γ ∈ ratPts σ J, ∃ q ∈ minParOne σ J X, ∃ s : Fin r → ℝ,
      (fun i => Real.exp (s i)) ∈ cone r c ∧ ∃ κ ∈ C, g = γ * q * a s * κ

theorem ratV_injective : Function.Injective (ratV F : (Fin n → E) → Fin n → AF F ⊗[F] E) := by
  intro u v h
  funext i
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  haveI : Nontrivial (AF F) := (evInf F w : AF F →+* w.Completion).domain_nontrivial
  exact Algebra.TensorProduct.includeRight_injective (algebraMap F (AF F)).injective (congrFun h i)

variable {σ J}

theorem Sends.inv {γ : GAd σ J} {u v : Fin n → E} (h : Sends σ J γ u v) : Sends σ J γ⁻¹ v u := by
  unfold Sends at h ⊢
  rw [← h, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mulVec]

theorem hgt_mul {γ g : GAd σ J} {u v : Fin n → E} (h : Sends σ J γ⁻¹ v u) : hgt σ J (γ⁻¹ * g) u = hgt σ J g v := by
  unfold Sends at h
  unfold hgt
  rw [← h, Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul]
  simp [_root_.mul_inv_rev]

end GlobalTheory.CompanionTheory.RedCov

end
