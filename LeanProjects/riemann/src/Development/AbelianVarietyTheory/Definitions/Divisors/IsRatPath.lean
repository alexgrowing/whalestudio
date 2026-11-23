import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsIsoFromNormalization
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

namespace GlobalTheory.Nef

def evAt {R : Type} [CommRing R] {X : Scheme.{0}} (ξ : Sp R ⟶ X) {U : X.Opens} (h : ⊤ ≤ ξ ⁻¹ᵁ U) : Γ(X, U) →+* R :=
  (Scheme.ΓSpecIso (.of R)).hom.hom.comp (ξ.appLE U ⊤ h).hom

section Path

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] {R : Type} [CommRing R]

def sqr : G.left ⟶ G.left := (𝟙 G * 𝟙 G : G ⟶ G).left

def triv (b : Sp R ⟶ S) : Sp (PowerSeries R) ⟶ G.left := spMap (PowerSeries.C (R := R)) ≫ b ≫ unitSec G

structure IsPath (c : R) (b : Sp R ⟶ S) (ξ : Sp (PowerSeries R) ⟶ G.left) : Prop where

  base : ξ ≫ G.hom = spMap (PowerSeries.C (R := R)) ≫ b

  zero : spMap (PowerSeries.constantCoeff (R := R)) ≫ ξ = b ≫ unitSec G

  scale : spMap (PowerSeries.rescale c) ≫ ξ = ξ ≫ sqr G

def HasTan {n : ℕ} (b : Sp R ⟶ S) (ξ : Sp (PowerSeries R) ⟶ G.left) {V : S.Opens} (τ : Fin n → Γ(Lie G, V))
    (w : Fin n → R) : Prop :=
  ∀ (U : G.left.Opens) (hU : ⊤ ≤ ξ ⁻¹ᵁ U) (V' : S.Opens) (hV : V' ≤ V) (he : V' ≤ unitSec G ⁻¹ᵁ U)
    (hb : ⊤ ≤ b ⁻¹ᵁ V') (f : Γ(G.left, U)),
    PowerSeries.coeff 1 (evAt ξ hU f) = ∑ i, w i * evAt b hb (dualApp (τ i) hV (dUnit G he f))

structure StalkData (s : S) (π : S.presheaf.stalk s →+* G.left.presheaf.stalk (unitSec G s))
    (ε : G.left.presheaf.stalk (unitSec G s) →+* S.presheaf.stalk s)
    (m : G.left.presheaf.stalk (unitSec G s) →+* G.left.presheaf.stalk (unitSec G s)) : Prop where

  str : Spec.map (CommRingCat.ofHom π) ≫ S.fromSpecStalk s = G.left.fromSpecStalk _ ≫ G.hom

  unit : Spec.map (CommRingCat.ofHom ε) ≫ G.left.fromSpecStalk _ = S.fromSpecStalk s ≫ unitSec G

  sq : Spec.map (CommRingCat.ofHom m) ≫ G.left.fromSpecStalk _ = G.left.fromSpecStalk _ ≫ sqr G

end Path

def IsRatPath {F : Type} [Field F] {Y : Scheme.{0}} (ξ : Sp (PowerSeries F) ⟶ Y) : Prop :=
  ∃ β : Sp (RatFunc F) ⟶ Y, spMap (algebraMap (RatFunc F) (LaurentSeries F)) ≫ β =
    spMap (algebraMap (PowerSeries F) (LaurentSeries F)) ≫ ξ

def RatRigid {S : Scheme.{0}} (G : Over S) [GrpObj G] {F : Type} [Field F] (b : Sp F ⟶ S) : Prop :=
  ∀ ξ : Sp (PowerSeries F) ⟶ G.left, IsPath G 2 b ξ → IsRatPath ξ → ξ = triv G b

def LocFrame {k K : Type} [Field k] [Field K] [Algebra k K] {C : Scheme.{0}} (x : Sp K ⟶ C) {W : C.Modules} {r : ℕ}
    {V₀ : C.Opens} (s : Fin r → Γ(W, V₀)) (v : Place k K) (g : Matrix (Fin r) (Fin r) K) : Prop :=
  ∃ (b : Sp v.O ⟶ C) (V : C.Opens) (t : Fin r → Γ(W, V)) (V' : C.Opens) (h₀ : V' ≤ V₀) (h₁ : V' ≤ V)
    (hx : ⊤ ≤ x ⁻¹ᵁ V') (M : Matrix (Fin r) (Fin r) Γ(C, V')),
    spMap v.O.subtype ≫ b = x ∧ ⊤ ≤ b ⁻¹ᵁ V ∧ IsFrame t ∧
      (∀ j, resM W h₀ (s j) = ∑ i, M i j • resM W h₁ (t i)) ∧ g = M.map (evAt x hx)

def IsGenOver (k : Type) {K : Type} [Field k] [Field K] [Algebra k K] {C : Scheme.{0}} [Algebra k Γ(C, ⊤)]
    (x : Sp K ⟶ C) : Prop :=
  NeronCurve.IsCurve k C ∧ NeronCurve.IsGen x ∧ x ≫ strHom k C = spMap (algebraMap k K)

theorem triv_over {S : Scheme.{0}} (G : Over S) [GrpObj G] {R : Type} [CommRing R] (b : Sp R ⟶ S) :
    triv G b ≫ G.hom = spMap (PowerSeries.C (R := R)) ≫ b := by
  rw [triv, Category.assoc, Category.assoc, sec_hom, Category.comp_id]

end GlobalTheory.Nef
