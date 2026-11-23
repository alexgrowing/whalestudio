import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FinalJoin2

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin
open scoped TensorProduct

def IntUnit {D : D7} (x : (AfE D)ˣ) : Prop := (x : AfE D) ∈ intAE D ∧ ((x⁻¹ : (AfE D)ˣ) : AfE D) ∈ intAE D

structure XiRec (D : D7) (p : ℕ) (de : (AfE D)ˣ →* ℂˣ) : Prop where
  real : ∀ (x : (AfE D)ˣ) (a : Af D.host.F), (x : AfE D) = a ⊗ₜ 1 → de x = 1
  rat : ∀ (x : (AfE D)ˣ) (a : D.host.E), (x : AfE D) = 1 ⊗ₜ a → de x = 1
  tame : ∀ x, IntUnit x → CongOne p x → de x = 1
  ram : ∃ x, IntUnit x ∧ CongOne (D.host.g 0 * D.host.g 1) x ∧ de x ≠ 1
  fin : ∃ m : ℕ, 0 < m ∧ ∀ x, de x ^ m = 1
  val : ∀ x, ((de x : ℂˣ) : ℂ) ∈ FO D

end GlobalTheory.FinalJoin2
