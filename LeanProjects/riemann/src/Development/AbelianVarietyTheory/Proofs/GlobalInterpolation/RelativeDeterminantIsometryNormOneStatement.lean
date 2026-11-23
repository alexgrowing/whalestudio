import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RelativeDeterminantIsometryNormOne
import Mathlib
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relativeDeterminant_isometry_norm_one : ∀ (D : D7) (γ₀ γ : IsoK D), ((γ.detRel γ₀ : D.host.K) : D.host.E) * D.host.conj ((γ.detRel γ₀ : D.host.K) : D.host.E) = 1 := by
  first | exact @GlobalTheory.detRel_mul_conj_eq_one | exact GlobalTheory.detRel_mul_conj_eq_one | (intros; apply GlobalTheory.detRel_mul_conj_eq_one <;> assumption)
