import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittLevelOneVanishAboveDim
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_level_one_vanish_above_dim : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O] {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (ρ : O →+* k) (U : Cov q) (d : ℕ), (∀ α, U.d α ≤ d) →
    ∀ j, Subsingleton (CH.H (sq (sFil (St (γ := Wc.pd l k 1) (p := l) (q := q) (κ := (Wc.res l k 1).comp ρ) ⊤ (Set.range U.U)) ((d : ℤ) + 1)) (IdF.bot _)) j) := by
  first | exact @GlobalTheory.CompanionTheory.WittLevel.Van.witt_level_one_filtration_vanish | exact GlobalTheory.CompanionTheory.WittLevel.Van.witt_level_one_filtration_vanish | (intros; apply GlobalTheory.CompanionTheory.WittLevel.Van.witt_level_one_filtration_vanish <;> assumption)
