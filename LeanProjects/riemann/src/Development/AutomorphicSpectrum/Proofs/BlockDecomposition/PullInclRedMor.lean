import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.IsFirstChernThickening
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.RedThick

theorem pull_incl_redMor : ∀ {O A R Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R] [CommRing Λ] {I : Ideal A} {γ : DividedPowers I}
    {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} {l n : ℕ} (d : RedIn δ κ γ l n) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) (s s' : ℕ) (𝒱 : Set X.Opens) (h : TS γ q l s 𝒱 ≤ TS γ q l s' 𝒱) (c : Λ →+* R) (lam : Λ →+* A)
    (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a)) (r : Option ℤ) (j : ℕ) (x : CH.H (B.OM (nlFun δ l X q κ) c) j),
    ((incl h).sq (a := IdF.top _) (a' := IdF.top _) (fun _ _ _ => trivial) (incl_std h r ((l : A) ^ n))).pull j
      ((redMor q s' d 𝒱 c lam hc r).pull j x) = (redMor q s d 𝒱 c lam hc r).pull j x := by
  intro O A R Λ _ _ _ _ _ I γ J δ κ l n d X q s s' 𝒱 h c lam hc r j x
  obtain ⟨⟨a, ha⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun u => ?_))
  change ((incl h).sq (a := IdF.top _) (a' := IdF.top _) (fun _ _ _ => trivial) (incl_std h r ((l : A) ^ n))).τ _
      ((redMor q s' d 𝒱 c lam hc r).τ _ (a (u ⋙ (ObjectProperty.ιOfLE h ⋙ redG q s' d 𝒱)))) =
    (redMor q s d 𝒱 c lam hc r).τ _ (a (u ⋙ redG q s d 𝒱))
  have key : ∀ z : (u.obj (Fin.last j)).obj.B ⧸ lnT (u.obj (Fin.last j)).obj l n,
      ((incl h).sq (a := IdF.top _) (a' := IdF.top _) (fun _ _ _ => trivial) (incl_std h r ((l : A) ^ n))).τ (u.obj (Fin.last j))
        ((redMor q s' d 𝒱 c lam hc r).τ ((ObjectProperty.ιOfLE h).obj (u.obj (Fin.last j))) z) =
      (redMor q s d 𝒱 c lam hc r).τ (u.obj (Fin.last j)) z := by
    intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    rfl
  exact key (a (u ⋙ redG q s d 𝒱))

end GlobalTheory.CompanionTheory.RedThick
