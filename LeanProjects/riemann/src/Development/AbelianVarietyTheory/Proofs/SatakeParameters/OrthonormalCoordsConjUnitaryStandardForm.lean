import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TwistEmptyOfChartsEx
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.LocalProductMeasures.MqRowSGUnif
import Formalism.SharpRestriction.GlobalSchurBounds.Joints
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.UG Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct

namespace GlobalTheory

theorem unitary_conj_orthonormal : ∀ (D : D7) {n : ℕ} (J : Matrix (Fin n) (Fin n) D.host.E) (crd γ : GL (Fin n) D.host.E), cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) (crd : Matrix (Fin n) (Fin n) D.host.E) * (crd : Matrix (Fin n) (Fin n) D.host.E) = J → γ ∈ UJ (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) J → cT (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) ((crd * γ * crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) * ((crd * γ * crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) = 1 := by
  intro D n J crd γ hc hγ
  set σ : D.host.E →+* D.host.E := (Formalism.L2.Forms.sigD D : D.host.E →+* D.host.E) with hσ
  have hg : cT σ (γ : Matrix (Fin n) (Fin n) D.host.E) * J * (γ : Matrix (Fin n) (Fin n) D.host.E) = J := hγ
  have h1 : (crd : Matrix (Fin n) (Fin n) D.host.E) * ((crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  simp only [Units.val_mul]
  rw [cT_mul, cT_mul]
  calc cT σ ((crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) * (cT σ (γ : Matrix (Fin n) (Fin n) D.host.E) * cT σ (crd : Matrix (Fin n) (Fin n) D.host.E)) *
        ((crd : Matrix (Fin n) (Fin n) D.host.E) * (γ : Matrix (Fin n) (Fin n) D.host.E) * ((crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E))
      = cT σ ((crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) * (cT σ (γ : Matrix (Fin n) (Fin n) D.host.E) * (cT σ (crd : Matrix (Fin n) (Fin n) D.host.E) * (crd : Matrix (Fin n) (Fin n) D.host.E)) * (γ : Matrix (Fin n) (Fin n) D.host.E)) * ((crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) := by
        simp only [Matrix.mul_assoc]
    _ = cT σ ((crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) * (cT σ (crd : Matrix (Fin n) (Fin n) D.host.E) * (crd : Matrix (Fin n) (Fin n) D.host.E)) * ((crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) := by
        rw [hc, hg, ← hc]
    _ = cT σ ((crd : Matrix (Fin n) (Fin n) D.host.E) * ((crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)) * ((crd : Matrix (Fin n) (Fin n) D.host.E) * ((crd⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E)) := by
        rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h1, cT_one, Matrix.one_mul]

end GlobalTheory
