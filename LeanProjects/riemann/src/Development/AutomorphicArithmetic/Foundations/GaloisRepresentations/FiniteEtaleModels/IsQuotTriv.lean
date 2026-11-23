import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.IntegOfMem
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.IsEtIdealOfPlace

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)

namespace UpperTheory.Gal.FiniteEtaleModels

structure IsQuot {E : Type} [Field E] {Γ : Type} [Group Γ] (X : G3.Tower (Sp E) Γ) (O : Type) [CommRing O] [Algebra O E]
    (K₀ : Subgroup Γ) (i : X.ι) {Y : Scheme.{0}} (pY : Y ⟶ Spec (CommRingCat.of O)) (π : X.Z i ⟶ Y) : Prop where
  ov : π ≫ pY = X.q i ≫ gen O E
  le : X.K i ≤ K₀
  idx : (X.K i).relIndex K₀ ≠ 0
  adm : ∀ u ∈ K₀, X.admitted i i u
  inv : ∀ u ∈ K₀, ∀ a b, X.tr i i u a b ≫ π = π
  fib : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x y : sp Ω ⟶ X.Z i), x ≫ π = y ≫ π → ∃ u ∈ K₀, ∃ a b, y = x ≫ X.tr i i u a b
  free : ∀ u ∈ K₀, ∀ a b (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : sp Ω ⟶ X.Z i), x ≫ X.tr i i u a b = x → u ∈ X.K i
  onto : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (y : sp Ω ⟶ Y) (σ : sp Ω ⟶ sp E), y ≫ pY = σ ≫ gen O E → ∃ x, x ≫ π = y

def DegGen : Prop :=
  ∀ (E : Type) [Field E] (Γ : Type) [Group Γ] (X : G3.Tower (Sp E) Γ) (O : Type) [CommRing O] [Algebra O E] (K₀ K₁ : Subgroup Γ) (i : X.ι)
    (Y Y' : Scheme.{0}) (pY : Y ⟶ Spec (CommRingCat.of O)) (π' : X.Z i ⟶ Y') (s : Y' ⟶ Y), K₁ ≤ K₀ →
    IsQuot X O K₀ i pY (π' ≫ s) → IsQuot X O K₁ i (s ≫ pY) π' →
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (y : sp Ω ⟶ Y) (σ : sp Ω ⟶ sp E), y ≫ pY = σ ≫ gen O E →
      Nat.card {y' : sp Ω ⟶ Y' // y' ≫ s = y} = K₁.relIndex K₀

def FEtExt : Prop :=
  ∀ (O E : Type) [CommRing O] [IsDomain O] [Field E] [Algebra O E] [IsFractionRing O E] (Y Y' : Scheme.{0})
    (pY : Y ⟶ Spec (CommRingCat.of O)) (s : Y' ⟶ Y) (d : ℕ), Flat pY → IsFinite s → Etale s →
    (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (y : sp Ω ⟶ Y) (σ : sp Ω ⟶ sp E), y ≫ pY = σ ≫ gen O E →
      Nat.card {y' : sp Ω ⟶ Y' // y' ≫ s = y} = d) → FEt s d

def SigmaFEt : Prop :=
  ∀ (Y Y' : Scheme.{0}) (s : Y' ⟶ Y) (d : ℕ) (I : Type) [Finite I], FEt s d → FEt (Sigma.desc fun _ : I => s) (Nat.card I * d)

def LiesAbs : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G) (E : Type) [Field E] [Algebra ℚ E] (gb : GBase D.toG E) (k : ℕ)
    (T : KS L gb k) (N : Lv p) (J A : Type) [Field A] (g : J → Mem L N) (θ : J → A) (O : Type) [CommRing O] [Algebra O E]
    (C : Cover (T.tower N g) θ O) (j : J) (K₀ K₁ : Subgroup G.GAf) (Y' : Scheme.{0}) (π' : T.X.Z (T.lev (g j).M) ⟶ Y') (s : Y' ⟶ C.Y) (d : ℕ),
    K₁ ≤ K₀ → L.KN N.1 ≤ K₀ → IsQuot T.X O K₀ (T.lev (g j).M) C.p (π' ≫ s) → IsQuot T.X O K₁ (T.lev (g j).M) (s ≫ C.p) π' →
    (∀ a b, T.X.tr (T.lev (g j).M) (T.lev N) 1 a b ≫ C.π = π' ≫ s) → FEt s d →
    (∀ u ∈ K₀, ∃ a ∈ (g j).K, a ∈ K₀ ∧ a⁻¹ * u ∈ K₁) →
    (∀ x ∈ (g j).K, ∃ t : Y' ⟶ C.Y, t ≫ C.p = s ≫ C.p ∧
      ∀ a b, π' ≫ t = T.X.tr (T.lev (g j).M) (T.lev N) ((g j).h * x) a b ≫ C.π) →
    ∃ (Z : Scheme.{0}) (s' t' : Z ⟶ C.Y) (d' m : ℕ), FEt s' d' ∧ t' ≫ C.p = s' ≫ C.p ∧ C.Lies j s' t' m

def LiftLev : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (G : HTGroup p) (L : Link D G), D.m = 1 → ∀ (q : ℕ) (r : ℤ) (𝔴 𝔞 : Ideal (𝓞 D.F)) (N₀ : ℕ),
    AtPrime D q r 𝔴 → (∃ e : ℕ, uId D q r ^ e ≤ 𝔞) → N₀.Coprime q → ∀ gg : LevGrp D 𝔞 1, ∃ u ∈ L.KN N₀,
      ∀ x y : D.La, gg ((wSub D 𝔞 1).mkQ x) = (wSub D 𝔞 1).mkQ y → L.actG u (inAf D x) - inAf D y ∈ idHat D 𝔞

def NormExt : Prop :=
  ∀ (U S Y B : Scheme.{0}) (i : U ⟶ S) (f : S ⟶ B) (g : Y ⟶ B) (y : U ⟶ Y), IsOpenImmersion i → IsDominant i → IsLocallyNoetherian S →
    (∀ x : S, IsDomain (S.presheaf.stalk x)) → (∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x)) → IsFinite g → y ≫ g = i ≫ f →
    ∃ y' : S ⟶ Y, i ≫ y' = y ∧ y' ≫ g = f

end UpperTheory.Gal.FiniteEtaleModels
