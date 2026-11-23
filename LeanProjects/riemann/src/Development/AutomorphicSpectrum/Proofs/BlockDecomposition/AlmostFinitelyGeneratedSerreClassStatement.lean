import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlmostFinitelyGeneratedSerreClass
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.almost_finitely_generated_serre_class : ∀ (R : Type) [CommRing R] (I : Ideal R) (c : R), I.FG → IsNilpotent I → I.IsPrime →
    (∀ x y : R, x ∈ Ideal.span {y} ⊔ I ∨ y ∈ Ideal.span {x} ⊔ I) → (∀ x : R, x ∉ I → ∃ n : ℕ, c ^ n ∈ Ideal.span {x} ⊔ I) →
    ∃ 𝒮 : Serre.{1} R, ∀ (M : Type 1) [AddCommGroup M] [Module R M], 𝒮.P M ↔ AFG c M := by
  first | exact @GlobalTheory.CompanionTheory.AlmostFinite.serre_afg | exact GlobalTheory.CompanionTheory.AlmostFinite.serre_afg | (intros; apply GlobalTheory.CompanionTheory.AlmostFinite.serre_afg <;> assumption)
