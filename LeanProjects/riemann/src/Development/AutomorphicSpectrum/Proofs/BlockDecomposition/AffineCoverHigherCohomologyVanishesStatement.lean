import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineCoverHigherCohomologyVanishes
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechSeparated
import GroundTheory.ArithmeticGeometry.SchemeCohomology.AffineVanishing
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_cover_higher_cohomology_vanishes : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} (str : ∀ W : X.Opens, O →+* Γ(X, W)) (W : X.Opens) (hW : IsAffineOpen W)
    {ι : Type} [Fintype ι] (U : ι → X.Opens) (hU : (⨆ α, U α) = W) (ha : ∀ n (i : Fin (n + 1) → ι), IsAffineOpen (capO U i))
    (K : Cos.{1} O) (V : VB str U K) (p : ℕ), Subsingleton (K.cx.H (p + 1)) := by
  first | exact @GlobalTheory.CompanionTheory.VBAff.subsingleton_H | exact GlobalTheory.CompanionTheory.VBAff.subsingleton_H | (intros; apply GlobalTheory.CompanionTheory.VBAff.subsingleton_H <;> assumption)
