import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MuBNat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullInclRedMor
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DPullCEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InclRedM
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResKOne
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.IsFirstChernThickening

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

theorem ts_le : ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (l : ℕ) {s s' : ℕ} (h : s ≤ s') (𝒱 : Set X.Opens), TS γ q l s 𝒱 ≤ TS γ q l s' 𝒱 := by
  intro O A _ _ _ I γ X q l s s' h 𝒱 T hT
  exact ⟨⟨le_bot_iff.1 ((T.pdPow_anti h).trans hT.1.1.le), hT.1.2⟩, hT.2⟩

theorem reduction_change_level : ∀ {O A R Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R] [CommRing Λ] {I : Ideal A} {γ : DividedPowers I}
    {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ} (d : RedIn δ κ γ l n) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (s s' : ℕ) (𝒱 : Set X.Opens) (h : TS γ q l s 𝒱 ≤ TS γ q l s' 𝒱) (c : Λ →+* R) (lam : Λ →+* A)
    (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a)) (r : Option ℤ) (j : ℕ) (x : CH.H (B.OM (nlFun δ l X q κ) c) j),
    ((incl h).sq (a := IdF.top _) (a' := IdF.top _) (fun _ _ _ => trivial) (incl_std h r ((l : A) ^ n))).pull j
      ((redMor q s' d 𝒱 c lam hc r).pull j x) = (redMor q s d 𝒱 c lam hc r).pull j x := @GlobalTheory.CompanionTheory.RedThick.pull_incl_redMor

theorem incl_redM : ∀ {b : Base} {L : b.Fun} {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) (r : Option ℤ) (c : b.R) (j : ℕ) (z : HO Q j),
    ((incl h).sq (a := IdF.top _) (a' := IdF.top _) (fun _ _ _ => trivial) (incl_std h r c)).pull j (redM Q r c j z) =
      redM Q' r c j ((incl h).o.pull j z) := @GlobalTheory.CompanionTheory.RedPull.incl_redM

theorem incl_muB : ∀ {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (l s s' : ℕ) (𝒱 : Set X.Opens) (h : TS γ q l s 𝒱 ≤ TS γ q l s' 𝒱) (j : ℕ) (x : HdR q j),
    (incl h).o.pull j (muB γ q l s' 𝒱 j x) = muB γ q l s 𝒱 j x := @GlobalTheory.CompanionTheory.MuThick.muB_incl

theorem nm_muB : ∀ {K B₁ B₂ : Type} [CommRing K] [CommRing B₁] [CommRing B₂] [Algebra K B₁] [Algebra K B₂] {I₁ : Ideal B₁} {I₂ : Ideal B₂}
    {γ₁ : DividedPowers I₁} {γ₂ : DividedPowers I₂} {X₁ X₂ : Scheme.{0}} {q₁ : X₁ ⟶ Spec (CommRingCat.of K)}
    {q₂ : X₂ ⟶ Spec (CommRingCat.of K)} {σ : B₁ →+* B₂} (nm : NMor γ₁ q₁ (κA K I₁) γ₂ q₂ (κA K I₂) σ) (hu : nm.u ≫ q₁ = q₂) (l s : ℕ),
    (∀ k, σ (algebraMap K B₁ k) = algebraMap K B₂ k) → ∀ (j : ℕ) (x : HdR q₁ j),
    nmHO nm l s j (muB γ₁ q₁ l s {⊤} j x) = muB γ₂ q₂ l s {⊤} j (pullR j nm.u hu x) := @GlobalTheory.CompanionTheory.MuNat.muB_nat

theorem muB_cup : ∀ {K B' : Type} [CommRing K] [CommRing B'] [Algebra K B'] {I : Ideal B'} (γ : DividedPowers I) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of K)) (l s : ℕ) (𝒱 : Set X.Opens), (∀ {i j k : ℕ} (h : i + j = k) (x : HdR q i) (y : HdR q j),
      muB γ q l s 𝒱 k (cupK q h x y) = (CH.mulP (sP (TS γ q l s 𝒱)).A).cup h (muB γ q l s 𝒱 i x) (muB γ q l s 𝒱 j y)) ∧
    muB γ q l s 𝒱 0 (oneK q) = CH.oneH (sP (TS γ q l s 𝒱)).A := @GlobalTheory.CompanionTheory.SiteCup.muB_cup

end CrystallineSemistableComparison.Pb
