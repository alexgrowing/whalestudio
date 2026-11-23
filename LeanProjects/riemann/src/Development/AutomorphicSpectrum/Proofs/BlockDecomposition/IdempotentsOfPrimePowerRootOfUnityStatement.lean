import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentsOfPrimePowerRootOfUnity
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotents_of_prime_power_root_of_unity : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), R.Val (l : A.U) → ∀ (n : ℕ) (ζ : OC l), IsPrimitiveRoot ζ (l ^ n) → ∀ z : A.U, z ^ l ^ n = 1 → ∃ e : ZMod (l ^ n) → A.A, (haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩; CompleteOrthogonalIdempotents e) ∧ ∀ c, A.sharp (e c) * (z - A.oC ζ ^ c.val) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RootsLC.exists_idempotents_of_root_of_unity | exact GlobalTheory.CompanionTheory.RootsLC.exists_idempotents_of_root_of_unity | (intros; apply GlobalTheory.CompanionTheory.RootsLC.exists_idempotents_of_root_of_unity <;> assumption)
