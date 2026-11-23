import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrystallineGradedPiecesDescription
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_graded_pieces_description : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (r : ℕ), (∀ z ∈ A.Fil0 r, ∃ w : A.W, z - algebraMap A.W A.Acr0 w * A.dxi0 r ∈ A.Fil0 (r + 1)) ∧ (∀ w : A.W, algebraMap A.W A.Acr0 w * A.dxi0 r ∈ A.Fil0 (r + 1) ↔ w ∈ Ideal.span {A.xi}) ∧ ∀ z ∈ A.Fil0 r, ∃ (N : ℕ) (w : A.W), (l : A.Acr0) ^ N * z = algebraMap A.W A.Acr0 (A.xi ^ r * w) := by
  first | exact @GlobalTheory.CompanionTheory.PerfFil.crystalline_filtration_graded_pieces | exact GlobalTheory.CompanionTheory.PerfFil.crystalline_filtration_graded_pieces | (intros; apply GlobalTheory.CompanionTheory.PerfFil.crystalline_filtration_graded_pieces <;> assumption)
