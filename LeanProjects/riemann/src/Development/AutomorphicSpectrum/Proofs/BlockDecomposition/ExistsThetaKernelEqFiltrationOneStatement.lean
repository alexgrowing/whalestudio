import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsThetaKernelEqFiltrationOne
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_theta_kernel_eq_filtration_one : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (n : ℕ), ∃ θ : A.Acr n →+* A.Un n, (∀ x : A.W, θ (A.toAcr n x) = Ideal.Quotient.mk _ (A.th x)) ∧ RingHom.ker θ = A.Fil n 1 := by
  first | exact @GlobalTheory.CompanionTheory.PerfectAlg.exists_theta_mod | exact GlobalTheory.CompanionTheory.PerfectAlg.exists_theta_mod | (intros; apply GlobalTheory.CompanionTheory.PerfectAlg.exists_theta_mod <;> assumption)
