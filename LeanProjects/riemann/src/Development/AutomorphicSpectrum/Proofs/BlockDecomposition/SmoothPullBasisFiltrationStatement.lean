import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothPullBasisFiltration
import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZKApply
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_pull_basis_filtration : ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (l s : ℕ) (𝒱 : Set X.Opens) (a : A) (t u r : ℤ) (ht : t ≤ 0)
    (ha : (smO γ q l s 𝒱).LeC a (sFil _ t) (sFil _ 0)) (hb : (smO γ q l s 𝒱).LeC a (sFil _ u) (sFil _ r)) (j : ℕ)
    (x : HdR q j),
    ((smO γ q l s 𝒱).sqC a ha hb).pull j (GlobalTheory.CompanionTheory.BasisBase.zK q (TO q l s 𝒱) t u ht j x) =
      quoM (TS γ q l s 𝒱) r j (a • muB γ q l s 𝒱 j x) := by
  first | exact @GlobalTheory.CompanionTheory.BasisBase.sqC_zK | exact GlobalTheory.CompanionTheory.BasisBase.sqC_zK | (intros; apply GlobalTheory.CompanionTheory.BasisBase.sqC_zK <;> assumption)
