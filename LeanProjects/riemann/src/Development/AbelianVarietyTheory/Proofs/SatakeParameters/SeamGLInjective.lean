import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemLatBack

noncomputable section

namespace GlobalTheory.TwU

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G
open scoped TensorProduct

def CongX {E : Type} [Field E] [NumberField E] {N : ℕ} (P : HeightOneSpectrum (𝓞 E)) (n : ℕ) (h : Sp E N ≃ₗ[E] Sp E N) : Prop :=
  ∀ a b, Formalism.L2.Col.IntAt P ((((qOf P : ℕ) : E) ^ n)⁻¹ * (LinearMap.toMatrix' h.toLinearMap - 1) a b)

section Seam

variable {D : D7} {X : Fields} (s : Seam D X)

def seamLE {n : ℕ} (g : GL (Fin n) D.host.E) : Sp X.E n ≃ₗ[X.E] Sp X.E n :=
  LinearMap.GeneralLinearGroup.generalLinearEquiv X.E (Fin n → X.E)
    (Matrix.GeneralLinearGroup.toLin (bc (s.iE.symm : D.host.E →+* X.E) g))

theorem seamGL_seamLE {n : ℕ} (g : GL (Fin n) D.host.E) : seamGL s (seamLE s g) = g := by
  ext a b
  simp [seamGL, seamLE, bc]

end Seam

end GlobalTheory.TwU

end
