import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharKer

variable {S : Scheme.{0}}

def pullTop {X Y : Scheme.{0}} (f : X ⟶ Y) : Γ(Y, ⊤)ˣ →* Γ(X, ⊤)ˣ := Units.map f.appTop.hom

def pmap {A A' : Over S} (q : A ⟶ A') (T : Over S) : A ⊗ T ⟶ A' ⊗ T := lift (fst A T ≫ q) (snd A T)

def actMap {A N : Over S} [GrpObj A] (i : N ⟶ A) (T : Over S) : A ⊗ (N ⊗ T) ⟶ A ⊗ T :=
  lift (fst A (N ⊗ T) * (snd A (N ⊗ T) ≫ fst N T ≫ i)) (snd A (N ⊗ T) ≫ snd N T)

def prMap (A N T : Over S) : A ⊗ (N ⊗ T) ⟶ A ⊗ T := lift (fst A (N ⊗ T)) (snd A (N ⊗ T) ≫ snd N T)

def IsCharacter {N T : Over S} [GrpObj N] (χ : Γ((N ⊗ T).left, ⊤)ˣ) : Prop :=
  pullTop (lift (fst N (N ⊗ T) * (snd N (N ⊗ T) ≫ fst N T)) (snd N (N ⊗ T) ≫ snd N T)).left χ =
    pullTop (lift (fst N (N ⊗ T)) (snd N (N ⊗ T) ≫ snd N T)).left χ * pullTop (snd N (N ⊗ T)).left χ

def IsPullGen {X Y : Scheme.{0}} (p : X ⟶ Y) (M : LB Y) (e : ∀ k, Γ(X, p ⁻¹ᵁ M.U k)ˣ) : Prop :=
  ∀ (k l : M.ι) (W : X.Opens) (h₁ : W ≤ p ⁻¹ᵁ M.U k) (h₂ : W ≤ p ⁻¹ᵁ M.U l) (h₃ : W ≤ p ⁻¹ᵁ (M.U k ⊓ M.U l)),
    res h₁ (e k) = res h₃ (pullU p _ (M.g k l)) * res h₂ (e l)

def IsEquivGen {A A' N T : Over S} [GrpObj A] (i : N ⟶ A) (q : A ⟶ A') (χ : Γ((N ⊗ T).left, ⊤)ˣ)
    (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ) : Prop :=
  IsPullGen (pmap q T).left M e ∧
    ∀ (k : M.ι) (W : (A ⊗ (N ⊗ T)).left.Opens)
      (h₁ : W ≤ (actMap i T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U k))
      (h₂ : W ≤ (prMap A N T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U k)),
      res h₁ (pullU (actMap i T).left _ (e k)) =
        res le_top (pullTop (snd A (N ⊗ T)).left χ) * res h₂ (pullU (prMap A N T).left _ (e k))

end GlobalTheory.CharKer
