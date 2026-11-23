import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.IsE8ThetaStructure

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegMin

def MinSt3 : Prop :=
  ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n),
    ∃ (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (_ : IsOpenImmersion i) (OZ : LB Z)
      (o' : Type) (_ : CommRing o') (β : cycAway n →+* o') (S' : Scheme.{0}) (s' : S' ⟶ Sp o') (U : S'.Opens)
      (c : U.toScheme ⟶ F.X) (π : S' ⟶ Z) (G : Over S') (_ : GrpObj G) (e : pullback F.univ.A.hom c ⟶ G.left)
      (_ : IsCommMonObj G) (L : LB G.left) (N : ℕ),
      (IsProjOver z ∧ IsNormalScheme Z ∧ i ≫ z = F.s ∧ Dense (Set.range i) ∧ OZ.IsLB ∧ IsAmpleLB OZ) ∧
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

end GlobalTheory.SiegMin
