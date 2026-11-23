import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinPolesStd
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledBasisSkewColumnMatrixGramInverse
open scoped NNReal Matrix TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn

theorem continuous_mat_pt (D : D7) (n : ℕ) : Continuous (mat : G D n → _) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_mat_pt_inv (D : D7) (n : ℕ) : Continuous (fun g : G D n => mat g⁻¹) :=
  Units.continuous_coe_inv.comp continuous_subtype_val

theorem continuous_of_mat_pt {D : D7} {n : ℕ} {X : Type} [TopologicalSpace X] {φ : X → G D n}
    (h : Continuous fun x => mat (φ x)) (h' : Continuous fun x => mat (φ x)⁻¹) : Continuous φ :=
  Continuous.subtype_mk (f := fun x => AdelicU.matHom _ D.sp.cm.sig (Jst D n) (φ x))
    (Units.continuous_iff.2 ⟨h, h'⟩) _

theorem chart_continuous : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → Continuous κ ∧ Continuous κ.symm := by
  intro D A μ hμ κ hκ
  have hT := (Tm_gram_inv D A μ hμ).2.1
  have h₁ : (rat (Tm A μ)⁻¹ : Formalism.IndefR.Datum.Mx D (A.rank + A.rank) (A.rank + A.rank)) * rat (Tm A μ) = 1 := by
    rw [← rat_mul, Matrix.nonsing_inv_mul _ hT, rat_one]
  have h₂ : (rat (Tm A μ) : Formalism.IndefR.Datum.Mx D (A.rank + A.rank) (A.rank + A.rank)) * rat (Tm A μ)⁻¹ = 1 := by
    rw [← rat_mul, Matrix.mul_nonsing_inv _ hT, rat_one]
  have e₁ : ∀ g, mat (κ g) = (rat (Tm A μ)⁻¹ : Formalism.IndefR.Datum.Mx D (A.rank + A.rank) (A.rank + A.rank)) *
      (Formalism.L2.Theta.mt (dblSp A) g * rat (Tm A μ)) := fun g => by
    rw [← hκ g, ← Matrix.mul_assoc, h₁, Matrix.one_mul]
  have e₂ : ∀ x, Formalism.L2.Theta.mt (dblSp A) (κ.symm x) =
      (rat (Tm A μ) : Formalism.IndefR.Datum.Mx D (A.rank + A.rank) (A.rank + A.rank)) * mat x * rat (Tm A μ)⁻¹ := fun x => by
    have := hκ (κ.symm x)
    rw [κ.apply_symm_apply] at this
    rw [this]
    exact ((Matrix.mul_assoc _ _ _).trans ((congrArg _ h₂).trans (Matrix.mul_one _))).symm
  have c₁ : Continuous fun g => mat (κ g) := by
    simp only [e₁]
    exact continuous_const.matrix_mul ((continuous_mt (dblSp A)).matrix_mul continuous_const)
  refine ⟨continuous_of_mat_pt c₁ ?_, continuous_of_mt (dblSp A) ?_⟩
  · simp only [← map_inv]
    exact c₁.comp continuous_inv
  · simp only [e₂]
    exact (continuous_const.matrix_mul (continuous_mat_pt D A.rank)).matrix_mul continuous_const

end GlobalTheory.StdUnn
