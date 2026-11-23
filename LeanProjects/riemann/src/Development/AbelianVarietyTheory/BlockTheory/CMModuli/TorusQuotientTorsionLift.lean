import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.TorusQuotientTorsionLift
open GlobalTheory.UU

def TorusStable {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] (i : splitTorus S X ⟶ G)
    (V : G.left.Opens) : Prop :=
  ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G), ⊤ ≤ g.left ⁻¹ᵁ V → ⊤ ≤ ((t ≫ i) * g).left ⁻¹ᵁ V

def IsBaseChangeTQ {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G] {X : Type} [AddCommGroup X]
    (f : S' ⟶ S) (F : G'.left ⟶ G.left) (Q' : TQ G' X) (Q : TQ G X) (β : Q'.B.left ⟶ Q.B.left) : Prop :=
  TorusCompat f F Q'.i Q.i ∧ IsGrpPullback Q'.B Q.B f β ∧ Q'.q.left ≫ β = F ≫ Q.q.left

abbrev pt {S : Scheme.{0}} {R : Type} [CommRing R] (p : Spec (CommRingCat.of R) ⟶ S) : Over S := Over.mk p

def TQOfSplitExtCoord : Prop :=
  ∀ (S : Scheme.{0}) (E : SplitExt S) (G : Over S) [GrpObj G] (D : E.GtDatum G),
    ∃ (Q : TQ G E.X) (β : Q.B ≅ E.B), IsMonHom β.hom ∧ Q.q ≫ β.hom = D.q ∧ Q.i = D.i

def TQOfLevelCoord : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G),
    ∃ (Q : TQ (thickObj R I e G) D.X) (β : Q.B ≅ thickObj R I e D.P.A),
      IsMonHom β.hom ∧ Q.q ≫ β.hom = g.q ∧ Q.i = g.i

def TQOfTorusExtension : Prop :=
  ∀ (k : Type) [Field k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G] (E : TorusExtension G),
    letI := E.addCommGroup
    letI := E.grpB
    ∃ (Q : TQ G E.X) (β : Q.B ≅ E.B), IsMonHom β.hom ∧ Q.q ≫ β.hom = E.q ∧ Q.i = E.i

def WeightDecomp : Prop :=
  ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (i : splitTorus S X ⟶ G), IsMonHom i → ∀ V : G.left.Opens, IsAffineOpen V → TorusStable i V →
    ∀ u : Γ(G.left, V), ∃! c : X →₀ Γ(G.left, V), (∀ χ, IsWt i V (c χ) χ) ∧ (c.sum fun _ a => a) = u

def WeightDecompSections : Prop :=
  ∀ (S : Scheme.{0}) [CompactSpace S] (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (Q : TQ G X) (N : LB Q.B.left), N.IsLB →
    ∀ s ∈ secOn (N.pull Q.q.left) ⊤,
      ∃! c : X →₀ (∀ j, Γ(G.left, ⊤ ⊓ (N.pull Q.q.left).U j)),
        (∀ χ, c χ ∈ secOn (N.pull Q.q.left) ⊤ ∧ ∀ j, IsWt Q.i _ (c χ j) χ) ∧ (c.sum fun _ a => a) = s

def WeightBaseChange : Prop :=
  ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G' : Over S') (G : Over S) [GrpObj G'] [GrpObj G] (F : G'.left ⟶ G.left)
    (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (i' : splitTorus S' X ⟶ G') (i : splitTorus S X ⟶ G), IsGrpPullback G' G f F → TorusCompat f F i' i →
    ∀ (V : G.left.Opens) (u : Γ(G.left, V)) (χ : X), IsWt i V u χ → IsWt i' (F ⁻¹ᵁ V) ((F.app V).hom u) χ

def WeightZero : Prop :=
  ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (Q : TQ G X) (V : Q.B.left.Opens) (u : Γ(G.left, Q.q.left ⁻¹ᵁ V)),
    IsWt Q.i _ u 0 ↔ ∃! a : Γ(Q.B.left, V), (Q.q.left.app V).hom a = u

def TorusLift : Prop :=
  ∀ (A : Type) [CommRing A] [IsLocalRing A] (J : Ideal A), IsNilpotent J →
    ∀ (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G], Smooth G.hom →
    ∀ (G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G₀] (F : G₀.left ⟶ G.left), IsGrpPullback G₀ G (red J) F →
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i₀ : splitTorus _ X ⟶ G₀),
      IsMonHom i₀ → IsClosedImmersion i₀.left →
      ∃ i : splitTorus _ X ⟶ G, IsMonHom i ∧ IsClosedImmersion i.left ∧ TorusCompat (red J) F i₀ i ∧
        ∀ i' : splitTorus _ X ⟶ G, IsMonHom i' → TorusCompat (red J) F i₀ i' → i' = i

def TQLift : Prop :=
  ∀ (A : Type) [CommRing A] [IsLocalRing A] (J : Ideal A), IsNilpotent J →
    ∀ (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G], Smooth G.hom →
    ∀ (G₀ : Over (Spec (CommRingCat.of (A ⧸ J)))) [GrpObj G₀] (F : G₀.left ⟶ G.left), IsGrpPullback G₀ G (red J) F →
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (Q₀ : TQ G₀ X),
      ∃ (Q : TQ G X) (β : Q₀.B.left ⟶ Q.B.left), IsBaseChangeTQ (red J) F Q₀ Q β

def TQUnique : Prop :=
  ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (Q Q' : TQ G X), Q.i = Q'.i →
    ∃ β : Q.B ≅ Q'.B, IsMonHom β.hom ∧ Q.q ≫ β.hom = Q'.q ∧ ∀ δ : Q.B ⟶ Q'.B, Q.q ≫ δ = Q'.q → δ = β.hom

def TQBaseChange : Prop :=
  ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G' : Over S') (G : Over S) [GrpObj G'] [GrpObj G] (F : G'.left ⟶ G.left),
    IsGrpPullback G' G f F →
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (Q : TQ G X),
      ∃ (Q' : TQ G' X) (β : Q'.B.left ⟶ Q.B.left), IsBaseChangeTQ f F Q' Q β

def TQBaseChangeOfCompat : Prop :=
  ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G' : Over S') (G : Over S) [GrpObj G'] [GrpObj G] (F : G'.left ⟶ G.left),
    IsGrpPullback G' G f F →
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (Q' : TQ G' X) (Q : TQ G X),
      TorusCompat f F Q'.i Q.i →
      ∃ β : Q'.B.left ⟶ Q.B.left, IsBaseChangeTQ f F Q' Q β ∧
        ∀ δ : Q'.B.left ⟶ Q.B.left, Q'.q.left ≫ δ = F ≫ Q.q.left → δ = β

def TQDim : Prop :=
  ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (Q : TQ G X),
    (∀ g' : ℕ, SmoothOfRelativeDimension (g' + Module.finrank ℤ X) G.hom ↔ SmoothOfRelativeDimension g' Q.B.hom) ∧
    (Nonempty S → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → Module.finrank ℤ X ≤ g)

def PointLift : Prop :=
  ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (Q : TQ G X) (R : Type) [CommRing R] [IsLocalRing R] (p : Spec (CommRingCat.of R) ⟶ S) (b : pt p ⟶ Q.B),
    ∃ x : pt p ⟶ G, x ≫ Q.q = b

def TorsionLift : Prop :=
  ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (Q : TQ G X) (R : Type) [CommRing R] [IsLocalRing R] (p : Spec (CommRingCat.of R) ⟶ S)
    (N : ℕ), 1 ≤ N → (∀ u : Rˣ, ∃ v : Rˣ, v ^ N = u) →
    ∀ b : pt p ⟶ Q.B, b ^ N = 1 → ∃ x : pt p ⟶ G, x ^ N = 1 ∧ x ≫ Q.q = b

def TorsionKernel : Prop :=
  ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (Q : TQ G X) (Z : Over S) (N : ℕ) (x : Z ⟶ G), x ^ N = 1 →
    (x ≫ Q.q = 1 ↔ ∃! t : Z ⟶ splitTorus S X, t ^ N = 1 ∧ t ≫ Q.i = x)

def TorsionLiftHenselian : Prop :=
  ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], Smooth G.hom →
    ∀ (R : Type) [CommRing R] [HenselianLocalRing R] (p : Spec (CommRingCat.of R) ⟶ S) (N : ℕ), IsUnit (N : R) →
    ∀ x₀ : pt (red (IsLocalRing.maximalIdeal R) ≫ p) ⟶ G, x₀ ^ N = 1 →
      ∃! x : pt p ⟶ G, x ^ N = 1 ∧ red (IsLocalRing.maximalIdeal R) ≫ x.left = x₀.left

def TorsionCount : Prop :=
  ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (X : Type) [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] (Q : TQ G X) (g' : ℕ), SmoothOfRelativeDimension g' Q.B.hom →
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Spec (CommRingCat.of Ω) ⟶ S) (N : ℕ), (N : Ω) ≠ 0 →
      Nat.card {x : pt p ⟶ G // x ^ N = 1} = N ^ (2 * g' + Module.finrank ℤ X)

def TorusQuotientClaims : Prop :=
  TQOfSplitExtCoord ∧ TQOfLevelCoord ∧ TQOfTorusExtension ∧ WeightDecomp ∧ WeightDecompSections ∧ WeightBaseChange ∧
    WeightZero ∧ TorusLift ∧ TQLift ∧ TQUnique ∧ TQBaseChange ∧ TQBaseChangeOfCompat ∧ TQDim ∧ PointLift ∧
    TorsionLift ∧ TorsionKernel ∧ TorsionLiftHenselian ∧ TorsionCount

example {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] (i : splitTorus S X ⟶ G) :
    TorusStable i ⊤ := fun _ _ _ _ => le_top

example {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] (Q : TQ G X) (V : Q.B.left.Opens) :
    TorusStable Q.i (Q.q.left ⁻¹ᵁ V) := fun Z t g h => by
  have := Q.q_hom
  have e : ((t ≫ Q.i) * g) ≫ Q.q = g ≫ Q.q := by
    rw [MonObj.mul_comp, Category.assoc, Q.isKernel.w, ← Category.assoc, toUnit_unique (t ≫ toUnit _) (toUnit _),
      ← Hom.one_def, _root_.one_mul]
  rw [← Scheme.Hom.comp_preimage, ← Over.comp_left] at h ⊢
  rwa [e]

example {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] (Q : TQ G X) :
    IsBaseChangeTQ (𝟙 S) (𝟙 _) Q Q (𝟙 _) := by
  refine ⟨TorusCompat.refl _, ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩, by simp⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have a : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have b : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [a, b, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

end GlobalTheory.IndefiniteRowSideFullHecke.TorusQuotientTorsionLift
end
