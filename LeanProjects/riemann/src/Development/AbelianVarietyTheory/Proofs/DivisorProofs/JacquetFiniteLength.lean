import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetGroupMorphismBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open GlobalTheory.AbDual GlobalTheory.CechPic

namespace GlobalTheory.BirigidLift

theorem lift_div : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I), IsNilDP κ →
    ∀ (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left),
      IsGrpPullback A₀ A (spMap π) i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (l : (A₀ ⊗ A₀).left ⟶ (A ⊗ A).left), IsSquare i l →
    ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L →
    ∀ (P₀ Q₀ S₀ : LB (A₀ ⊗ A₀).left), P₀.IsLB → Q₀.IsLB → S₀.IsLB → LBIso Q₀ (LB.div S₀ P₀) →
    ∀ (P Q S : LB (A ⊗ A).left), P.IsLB → Q.IsLB → S.IsLB →
      HasGen (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → HasGen (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
      HasGen (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → HasGen (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
      HasGen (S.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → HasGen (S.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
      LBIso (P.pull l) P₀ → LBIso (Q.pull l) Q₀ → LBIso (S.pull l) S₀ → LBIso Q (LB.div S P) := by
  intro HG HD R R₀ _ _ I κ hκ π hπ hI g A₀ _ A _ i h hA hg l hl L hL aL P₀ Q₀ S₀ hP₀ hQ₀ hS₀ eQ₀ P Q S hP hQ hS
    tP₁ tP₂ tQ₁ tQ₂ tS₁ tS₂ eP eQ eS
  have hd : (LB.div S P).IsLB := LB.isLB_div hS hP
  have triv : ∀ (a b : A ⟶ A), HasGen (S.pull (lift a b).left) → HasGen (P.pull (lift a b).left) →
      GlobalTheory.AbLaw.Triv (ev (LB.div S P) a b) := by
    intro a b t₁ t₂
    rw [triv_ev_iff hd, evc, cls_div hS hP hd, map_sub]
    have z₁ := (cls_eq_zero_iff (pull_isLB hS (lift a b).left)).2 t₁
    have z₂ := (cls_eq_zero_iff (pull_isLB hP (lift a b).left)).2 t₂
    rw [cls_pull hS] at z₁
    rw [cls_pull hP] at z₂
    rw [z₁, z₂, sub_zero]
  have red : LBIso ((LB.div S P).pull l) Q₀ := by
    refine (cls_eq_iff (pull_isLB hd l) hQ₀).1 ?_
    rw [cls_pull hd, cls_div hS hP hd, map_sub, ← cls_pull hS l (pull_isLB hS l), ← cls_pull hP l (pull_isLB hP l),
      (cls_eq_iff (pull_isLB hS l) hS₀).2 eS, (cls_eq_iff (pull_isLB hP l) hP₀).2 eP,
      (cls_eq_iff hQ₀ (LB.isLB_div hS₀ hP₀)).2 eQ₀, cls_div hS₀ hP₀]
  exact lift_unique HG HD.1 hκ hπ hI hA hg hA hg h h hl.1 hl.2 hL aL hL aL hQ₀ hQ tQ₁ tQ₂ eQ hd
    (triv _ _ tS₁ tP₁) (triv _ _ tS₂ tP₂) red

end GlobalTheory.BirigidLift
