import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

def DefOver {K : Type} [Field K] (k₀ : Subfield K) {Y : Scheme.{0}} (P : Sp K ⟶ Y) : Prop :=
  ∃ P₀ : Sp k₀ ⟶ Y, spMap k₀.subtype ≫ P₀ = P

variable {V : Type} [CommRing V] [IsDomain V]

abbrev Gens (Q : Data V) : Type := ∀ a b : Q.X, LB.Gen (LB.LinComb Q.M.L (lamPts (Q.c a) (Q.c b)) negε)

def TauIn (Q : Data V) (τ₀ : Gens Q) {N : ℕ} (s : Fin N → V) (ε : Fin N → LinearMap.BilinForm ℤ Q.X) : Prop :=
  ∀ a b, (τ₀ a b).IsGen ∧ ∃ k : (FractionRing V)ˣ,
    (k : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ε i a b ∧ ∀ z J, Good Q.M.L z J →
      val (Q.tau a b) (𝟙 _) z J = gm (𝟙 (TK V).left) z ⊤ (unitOn k) * val (τ₀ a b) (toUnit (TK V)).left z J

def FromBase (Q : Data V) (τ₀ : Gens Q) {W₀ : Type} [CommRing W₀] (ιb : W₀ →+* V) : Prop :=
  ∃ (B₀ : Over (Sp W₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (𝟙_ (Over (Sp W₀)) ⟶ B₀))
    (τ₁ : ∀ a b : Q.X, LB.Gen (LB.LinComb M₀ (lamPts (c₀ a) (c₀ b)) negε))
    (β : Q.B.left ⟶ B₀.left) (β₂ : (G2 Q.B).left ⟶ (G2 B₀).left)
    (w : LB.Iso (abelian₂ Q.B Q.M.L) ((abelian₂ B₀ M₀).pull β₂)),
    IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback Q.B B₀ (spMap ιb) β ∧ IsSquare β β₂ ∧ w.IsGen ∧
    (∀ a, (Q.c a).left ≫ β = spMap ιb ≫ (c₀ a).left) ∧ (∀ a b, (τ₁ a b).IsGen) ∧
    ∀ (T : Over (Sp V)) (a b : Q.X) z J J', Good M₀ z J → Good Q.M.L z J' →
      val (τ₀ a b) (toUnit T).left z J' =
        lamVal w (lift (toUnit T ≫ Q.c a) (toUnit T ≫ Q.c b)).left z J J' * val (τ₁ a b) (T.hom ≫ spMap ιb) z J

def UnifOver {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (j : F.X ⟶ S) [IsLocalRing V]
    (ξ : Sp V ⟶ S) (Q : Data V) : Prop :=
  IsCN V ∧ ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : V →+* R'), IsCN R' → Function.Injective ρ →
    ρ.Finite → ∀ (D : DegData R' (maximalIdeal R')) (ε : D.toPre.X ≃+ Q.X), Refines Q ρ D.toPre ε →
      ∃ (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (A : PolAV (Sp (FractionRing R')))
        (_ : Unif (maximalIdeal R') D A G') (y' : Sp (FractionRing R') ⟶ F.X) (α : A.A.left ⟶ F.univ.A.left)
        (α₂ : (G2 A.A).left ⟶ (G2 F.univ.A).left),
        IsSemiAbelian G' ∧ y' ≫ j = jK R' ≫ spMap ρ ≫ ξ ∧ IsGrpPullback A.A F.univ.A y' α ∧
          IsSquare α α₂ ∧ LBIso (abelian₂ A.A A.L) (F.univ.P.pull α₂)

def SepAt (Q : Data V) (τ₀ : Gens Q) {m N : ℕ} (s : Fin m ⊕ Fin N → V) {K : Type} [Field K] (ev : V →+* K)
    (k₀ : Subfield K) : Prop :=
  (∀ i, ev (s (.inl i)) = 0) ∧
  (∀ (o' : Type) [CommRing o'] (ζ' : o') (g' n' : ℕ) (F' : SFam g' n' ζ') (lam : Sp V ⟶ F'.X) (β : Q.B.left ⟶ F'.univ.A.left)
      (β₂ : (G2 Q.B).left ⟶ (G2 F'.univ.A).left), 1 ≤ n' → DefOver k₀ (spMap ev ≫ lam ≫ F'.s) →
      IsGrpPullback Q.B F'.univ.A lam β → IsSquare β β₂ → LBIso (abelian₂ Q.B Q.M.L) (F'.univ.P.pull β₂) →
      ∀ a, DefOver k₀ (spMap ev ≫ (Q.c a).left ≫ β)) ∧
  ∀ (W₀ : Type) [CommRing W₀] (ιb : W₀ →+* V), FromBase Q τ₀ ιb → (∀ a, ev (ιb a) ∈ k₀) → ∀ i, ev (s i) ∈ k₀

def SepSt : Prop :=
  ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n))
    (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ →
    ∀ (d : ℕ) (J : Z.IdealSheafData) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S), 1 ≤ d →
      (∀ x ∈ J.support, x ∉ Set.range i) → ValOn F i φ J d → IsNormBl π J → j ≫ π = i →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (ξ : Sp V ⟶ S), UnifOver F j ξ Q →
    ∀ (m N : ℕ) (s : Fin m ⊕ Fin N → V) (ε : Module.Basis (Fin m ⊕ Fin N) ℤ (balForms (id : ℤ → ℤ) Q.X)) (τ₀ : Gens Q),
      Module.finrank ℤ Q.X ≤ g → IsCone id φ (fun k => (ε (.inl k) : LinearMap.BilinForm ℤ Q.X)) →
      (∀ x, x ≠ 0 → ∃ k, 0 < (ε (.inl k) : LinearMap.BilinForm ℤ Q.X) x x) →
      (∀ k, s (.inl k) ∈ maximalIdeal V ∧ s (.inl k) ≠ 0) → (∀ k, IsUnit (s (.inr k))) →
      TauIn Q τ₀ (fun k => s (finSumFinEquiv.symm k))
        (fun k => (n : ℤ) • (ε (finSumFinEquiv.symm k) : LinearMap.BilinForm ℤ Q.X)) →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
      (∀ p, (spMap ev ≫ ξ) p = ξ (closedPoint V)) → DefOver k₀ (spMap ev ≫ ξ) → SepAt Q τ₀ s ev k₀

end GlobalTheory.Poinc.Sep
