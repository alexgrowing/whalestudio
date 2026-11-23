import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineFiltrationMultiplicative
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_filtration_multiplicative : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), A.Fil0 0 = ⊤ ∧ (∀ i j, A.dxi0 i * A.dxi0 j = ((i + j).choose i : A.Acr0) * A.dxi0 (i + j)) ∧ (∀ k, (k.factorial : A.Acr0) * A.dxi0 k = algebraMap A.W A.Acr0 A.xi ^ k) ∧ (∀ r s, A.Fil0 r * A.Fil0 s ≤ A.Fil0 (r + s)) ∧ (∀ n r, A.Fil n r = (A.Fil0 r).map (A.mkAcr n)) ∧ (∀ n, A.PFil n = A.PFil0.map (A.mkAcr n)) ∧ (∀ n, A.Fil n 0 = ⊤) ∧ ∀ n r s, A.Fil n r * A.Fil n s ≤ A.Fil n (r + s) := by
  first | exact @GlobalTheory.CompanionTheory.FilMul.main | exact GlobalTheory.CompanionTheory.FilMul.main | (intros; apply GlobalTheory.CompanionTheory.FilMul.main <;> assumption)
