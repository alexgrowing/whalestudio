import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsThetaVectorFamilyOfCurveDatum
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaVectorFamily_of_curveDatum : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∃ (χ : IdE D → ℂ) (e : FamE D), IsChi D χ ∧ vec22 D (tor0 D cc δ) e ∧ eq22 D (tor0 D cc δ) χ e := by
  first | exact @GlobalTheory.TrueTheta.exists_family_of_curve | exact GlobalTheory.TrueTheta.exists_family_of_curve | (intros; apply GlobalTheory.TrueTheta.exists_family_of_curve <;> assumption)
