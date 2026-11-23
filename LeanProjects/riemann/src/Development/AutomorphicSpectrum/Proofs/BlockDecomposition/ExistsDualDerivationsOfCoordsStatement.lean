import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDualDerivationsOfCoords
import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dual_derivations_of_coords : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (V : X.Opens) (d : ℕ) (c : Coord q V d), letI := (strV q V).toAlgebra; ∃ D : Fin d → Derivation K Γ(X, V) Γ(X, V), ∀ k j, D k (c.t j) = if k = j then 1 else 0 := by
  first | exact @GlobalTheory.CompanionTheory.ConeDerivs.exists_dual_derivations | exact GlobalTheory.CompanionTheory.ConeDerivs.exists_dual_derivations | (intros; apply GlobalTheory.CompanionTheory.ConeDerivs.exists_dual_derivations <;> assumption)
