import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.IsFirstChernThickening
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullUnitClass
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.SiteCup

variable {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

theorem resK_cup (Q : ObjectProperty (Thick (smFun X q))) {i j k : ℕ} (h : i + j = k) (x : HdR q i) (y : HdR q j) :
    resK q Q k (cupK q h x y) = (CH.mulP (sP Q).A).cup h (resK q Q i x) (resK q Q j y) :=
  CrystallineSemistableComparison.P.cup_pull (CH.mulP (thA (smFun X q))) (CH.mulP (sP Q).A) Q.ι
    (CH.Mor.restrict (CH.modF (thA (smFun X q))) Q.ι).τ (CH.Mor.restrict (CH.modF (thA (smFun X q))) Q.ι).τ
    (CH.Mor.restrict (CH.modF (thA (smFun X q))) Q.ι).τ (CH.Mor.restrict (CH.modF (thA (smFun X q))) Q.ι).nat
    (CH.Mor.restrict (CH.modF (thA (smFun X q))) Q.ι).nat (CH.Mor.restrict (CH.modF (thA (smFun X q))) Q.ι).nat
    (fun _ _ _ => rfl) h x y

theorem resK_one (Q : ObjectProperty (Thick (smFun X q))) : resK q Q 0 (oneK q) = CH.oneH (sP Q).A :=
  pull_unit_class (thA (smFun X q)) (sP Q).A (CH.Mor.restrict (CH.modF (thA (smFun X q))) Q.ι) fun _ => rfl

theorem muB_cup : ∀ {K B' : Type} [CommRing K] [CommRing B'] [Algebra K B'] {I : Ideal B'} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of K)) (l s : ℕ) (𝒱 : Set X.Opens), (∀ {i j k : ℕ} (h : i + j = k) (x : HdR q i) (y : HdR q j),
      muB γ q l s 𝒱 k (cupK q h x y) = (CH.mulP (sP (TS γ q l s 𝒱)).A).cup h (muB γ q l s 𝒱 i x) (muB γ q l s 𝒱 j y)) ∧
    muB γ q l s 𝒱 0 (oneK q) = CH.oneH (sP (TS γ q l s 𝒱)).A := by
  intro K B' _ _ _ I γ X q l s 𝒱
  refine ⟨fun {i j k} h x y => ?_, ?_⟩
  · change (smO γ q l s 𝒱).o.pull k (resK q (TO q l s 𝒱) k (cupK q h x y)) =
      (CH.mulP (sP (TS γ q l s 𝒱)).A).cup h ((smO γ q l s 𝒱).o.pull i (resK q (TO q l s 𝒱) i x))
        ((smO γ q l s 𝒱).o.pull j (resK q (TO q l s 𝒱) j y))
    rw [resK_cup]
    exact (smor_cup (smO γ q l s 𝒱)).1 h _ _
  · change (smO γ q l s 𝒱).o.pull 0 (resK q (TO q l s 𝒱) 0 (oneK q)) = _
    rw [resK_one]
    exact (smor_cup (smO γ q l s 𝒱)).2

end GlobalTheory.CompanionTheory.SiteCup
