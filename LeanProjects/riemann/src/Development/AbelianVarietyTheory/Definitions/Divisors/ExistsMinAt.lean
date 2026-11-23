import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegJoin

open GlobalTheory.SiegMin GlobalTheory.Poinc GlobalTheory.PolDeg

variable {g n : ℕ}

def MinAt (F : SFam g n (zetaAway n)) {Z : Scheme.{0}} (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) : Prop :=
  ∃ (o' : Type) (_ : CommRing o') (β : cycAway n →+* o') (S' : Scheme.{0}) (s' : S' ⟶ Sp o') (U : S'.Opens)
    (c : U.toScheme ⟶ F.X) (π : S' ⟶ Z) (G : Over S') (_ : GrpObj G) (e : pullback F.univ.A.hom c ⟶ G.left)
    (_ : IsCommMonObj G) (L : LB G.left) (N : ℕ),
    (IsThetaCompact F z i ∧ IsProjOver z ∧ IsNormalScheme Z ∧ i ≫ z = F.s ∧ Dense (Set.range i) ∧ OZ.IsLB ∧ IsAmpleLB OZ) ∧
    (β.Finite ∧ Function.Injective β ∧ IsProjOver s' ∧ IsNormalScheme S' ∧ Dense (U : Set S') ∧ IsFinite c ∧
      Surjective c ∧ U.ι ≫ π = c ≫ i ∧ π ⁻¹' Set.range i = U ∧ π ≫ z = s' ≫ spMap β ∧ Surjective π ∧ IsProper π ∧
      IsNoetherian Z) ∧
    (IsSemiAbelian G ∧ SmoothOfRelativeDimension g G.hom ∧
      IsGrpPullback ((Over.pullback c).obj F.univ.A) G U.ι e ∧ abLocus G = U) ∧
    (1 ≤ N ∧ LBIso (OZ.pull π) (lbPow (hodge G g) N)) ∧
    (L.IsLB ∧ ∃ (α₂ : (G2 ((Over.pullback c).obj F.univ.A)).left ⟶ (G2 F.univ.A).left)
      (e₂ : (G2 ((Over.pullback c).obj F.univ.A)).left ⟶ (G2 G).left),
      IsSquare (pullback.fst F.univ.A.hom c) α₂ ∧ IsSquare e e₂ ∧ LBIso ((abelian₂ G L).pull e₂) (lbPow (F.univ.P.pull α₂) 2)) ∧
    ∀ (K : Type) [Field K] [IsAlgClosed K] (x y : Sp K ⟶ S'), x ≫ π = y ≫ π → SameAbPart G x y

def BlowAt (F : SFam g n (zetaAway n)) {Z : Scheme.{0}} (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (φ : InvFun ℤ) (d : ℕ)
    {S : Scheme.{0}} (π : S ⟶ Z) (j : F.X ⟶ S) (BD : EffCartierData S) : Prop :=
  ∃ J : Z.IdealSheafData, 1 ≤ d ∧ (∀ x ∈ J.support, x ∉ Set.range i) ∧ ValOn F i φ J d ∧ IsNormBl π J ∧
    IsProjOver (π ≫ z) ∧ Dense (Set.range j) ∧ j ≫ π = i ∧ π ⁻¹' Set.range i = Set.range j ∧
    BD.idealSheaf = J.comap π ∧ ValOn F j φ BD.idealSheaf d

def ChartSt : Prop :=
  ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n →
    ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ)
      (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S),
      MinAt F z i OZ → BlowAt F z i φ d π j BD →
      SmoothOfRelativeDimension (g * (g + 1) / 2) (π ≫ z) ∧ ∀ x : S, PreChart F (π ≫ z) j φ BD d x

def DescSt : Prop :=
  ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, ∀ n : ℕ, 3 ≤ n → Odd n →
    ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ)
      (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S),
      MinAt F z i OZ → BlowAt F z i φ d π j BD → SmoothOfRelativeDimension (g * (g + 1) / 2) (π ≫ z) →
      (∀ x : S, PreChart F (π ≫ z) j φ BD d x) →
      ∃ (G : Over S) (_ : GrpObj G) (e : F.univ.A.left ⟶ G.left), IsSemiAbelian G ∧ SmoothOfRelativeDimension g G.hom ∧
        IsGrpPullback F.univ.A G j e ∧ abLocus G = Set.range j

end GlobalTheory.SiegJoin
