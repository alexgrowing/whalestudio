import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QMatInjective
noncomputable section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GroundTheory.Automorphic
open scoped InnerProductSpace Topology ENNReal NNReal ComplexConjugate

namespace GlobalTheory.CompanionTheory.ModP.StabEquiv

variable {n a : ℕ} {ε : Fin n → Bool} {W : Flag n a}

theorem uMat_mul' (g h : UJ ε) : uMat (g * h) = uMat g * uMat h := rfl

theorem uMat_one' : uMat (1 : UJ ε) = 1 := rfl

theorem uMat_mul_inv' (g : UJ ε) : uMat g * uMat g⁻¹ = 1 := by
  rw [← uMat_mul', mul_inv_cancel, uMat_one']

theorem uMat_inv_mul' (g : UJ ε) : uMat g⁻¹ * uMat g = 1 := by
  rw [← uMat_mul', inv_mul_cancel, uMat_one']

instance topAddGroup_qAlg (ε : Fin n → Bool) (W : Flag n a) : IsTopologicalAddGroup (qAlg ε W) :=
  inferInstanceAs (IsTopologicalAddGroup (Subalgebra.toSubmodule (qAlg ε W)))

instance continuousSMul_qAlg (ε : Fin n → Bool) (W : Flag n a) : ContinuousSMul ℝ (qAlg ε W) :=
  ⟨Continuous.subtype_mk
    (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)) _⟩

def toUnit (p : UJ ε) (h : uMat p ∈ qAlg ε W) (h' : uMat p⁻¹ ∈ qAlg ε W) : (QA ε W)ˣ where
  val := RegNorm.toRegNorm (qAlg ε W) ⟨uMat p, h⟩
  inv := RegNorm.toRegNorm (qAlg ε W) ⟨uMat p⁻¹, h'⟩
  val_inv := qMat_injective (by
    rw [qMat_mul, qMat_one]; exact uMat_mul_inv' p)
  inv_val := qMat_injective (by
    rw [qMat_mul, qMat_one]; exact uMat_inv_mul' p)

def toUJ (g : qGroup ε W) : UJ ε :=
  ⟨⟨qMat ((g : (QA ε W)ˣ) : QA ε W), qMat (((g : (QA ε W)ˣ)⁻¹ : (QA ε W)ˣ) : QA ε W),
    by rw [← qMat_mul, Units.mul_inv, qMat_one], by rw [← qMat_mul, Units.inv_mul, qMat_one]⟩, by
    have h := congrArg qMat ((mem_formGroup _ _ _ _).1 g.2)
    simp only [Units.val_one, mul_one, qMat_mul, qMat_qAdj, qMat_one, jAdj_apply] at h
    change (qMat ((g : (QA ε W)ˣ) : QA ε W))ᴴ * Jm ε * qMat ((g : (QA ε W)ˣ) : QA ε W) = Jm ε
    calc _ = Jm ε * (Jm ε * (qMat ((g : (QA ε W)ˣ) : QA ε W))ᴴ * Jm ε * qMat ((g : (QA ε W)ˣ) : QA ε W)) := by
          simp only [← Matrix.mul_assoc, Jm_mul_self, Matrix.one_mul]
      _ = Jm ε := by rw [h, Matrix.mul_one]⟩

end GlobalTheory.CompanionTheory.ModP.StabEquiv

namespace GlobalTheory.CompanionTheory.ModP

end GlobalTheory.CompanionTheory.ModP
