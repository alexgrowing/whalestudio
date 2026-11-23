import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegMin

def ThetaOn {S : Scheme.{0}} (G : Over S) (L : LB G.left) (δ : LB S) : Prop :=
  δ.IsLB ∧ ∃ σ : (CechPic.tens L (δ.pull G.hom)).Sec,
    ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S), ∃ (y : Sp K ⟶ G.left) (j : (CechPic.tens L (δ.pull G.hom)).ι),
      y ≫ G.hom = x ∧ valF y _ (σ.f j) ≠ 0

def SameAbPart {S : Scheme.{0}} (G : Over S) [GrpObj G] {K : Type} [Field K] (x y : Sp K ⟶ S) : Prop :=
  ∃ (E E' : SplitExt (Sp K)) (φ : E.B ≅ E'.B), E.IsGt ((Over.pullback x).obj G) ∧ E'.IsGt ((Over.pullback y).obj G) ∧
    Module.finrank ℤ E.X = Module.finrank ℤ E'.X ∧ IsMonHom φ.hom

def IsFormBundleOn {X S T : Scheme.{0}} {A : Over X} (P : LB (G2 A).left) {G H : Over S} (U : S.Opens) (α : T ⟶ A.left)
    (e : T ⟶ G.left) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (pr : Fin r → (H ⟶ G)) (L : LB H.left) : Prop :=
  ∃ (p : Fin r → ((H.hom ⁻¹ᵁ U).toScheme ⟶ T)) (q : Fin r × Fin r → ((H.hom ⁻¹ᵁ U).toScheme ⟶ (G2 A).left)),
    (∀ u, p u ≫ e = (H.hom ⁻¹ᵁ U).ι ≫ (pr u).left) ∧
    (∀ uv, q uv ≫ (fst A A).left = p uv.1 ≫ α ∧ q uv ≫ (snd A A).left = p uv.2 ≫ α) ∧
    LBIso (L.pull (H.hom ⁻¹ᵁ U).ι) (LB.LinComb P q fun uv => W uv.1 uv.2)

def IsE8ThetaStructure {X S T : Scheme.{0}} {A : Over X} (P : LB (G2 A).left) (G : Over S) [GrpObj G] (U : S.Opens)
    (α : T ⟶ A.left) (e : T ⟶ G.left) (δ : LB S) : Prop :=
  ∃ (W : Matrix (Fin 8) (Fin 8) ℤ) (H : Over S) (_ : GrpObj H) (_ : IsCommMonObj H) (pr : Fin 8 → (H ⟶ G)) (L : RigLB H),
    IsE8 W ∧ (∀ u, IsMonHom (pr u)) ∧ (∀ (Y : Over S) (y : Fin 8 → (Y ⟶ G)), ∃! x : Y ⟶ H, ∀ u, x ≫ pr u = y u) ∧
    L.IsSymmetric ∧ Nonempty (CubicalStr H L) ∧ IsFormBundleOn P U α e W pr L.L ∧ ThetaOn H L.L δ

def MinSt : Prop :=
  ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n),
    ∃ (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (_ : IsOpenImmersion i) (OZ : LB Z)
      (o' : Type) (_ : CommRing o') (β : cycAway n →+* o') (S' : Scheme.{0}) (s' : S' ⟶ Sp o') (U : S'.Opens)
      (c : U.toScheme ⟶ F.X) (π : S' ⟶ Z) (G : Over S') (_ : GrpObj G) (e : pullback F.univ.A.hom c ⟶ G.left)
      (δ : LB S') (N : ℕ),
      (IsProjOver z ∧ IsNormalScheme Z ∧ i ≫ z = F.s ∧ Dense (Set.range i) ∧ OZ.IsLB ∧ IsAmpleLB OZ) ∧
      (β.Finite ∧ Function.Injective β ∧ IsProjOver s' ∧ IsNormalScheme S' ∧ Dense (U : Set S') ∧ IsFinite c ∧
        Surjective c ∧ U.ι ≫ π = c ≫ i ∧ π ⁻¹' Set.range i = U ∧ π ≫ z = s' ≫ spMap β ∧ Surjective π) ∧
      (IsSemiAbelian G ∧ IsCommMonObj G ∧ SmoothOfRelativeDimension g G.hom ∧
        IsGrpPullback ((Over.pullback c).obj F.univ.A) G U.ι e ∧ abLocus G = U) ∧
      (1 ≤ N ∧ IsE8ThetaStructure F.univ.P G U (pullback.fst F.univ.A.hom c) e δ ∧ LBIso (OZ.pull π) (lbPow δ N)) ∧
      ∀ (K : Type) [Field K] [IsAlgClosed K] (x y : Sp K ⟶ S'), x ≫ π = y ≫ π → SameAbPart G x y

end GlobalTheory.SiegMin
