import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.IsKumCoc

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison

def E.LineData.pb {X X' : Scheme.{0}} (D : E.LineData X) (f : X' ⟶ X) : E.LineData X' where
  Y := pullback D.f f
  f := pullback.snd D.f f
  sm := by have := D.sm; infer_instance
  surj := by have := D.surj; infer_instance
  u a b h := D.u (a ≫ pullback.fst _ _) (b ≫ pullback.fst _ _)
    (by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, h, Category.assoc])
  nat g a b h := by
    have := D.nat g (a ≫ pullback.fst _ _) (b ≫ pullback.fst _ _)
      (by rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc, h, Category.assoc])
    simpa only [Category.assoc] using this
  coc a b c h h' := D.coc _ _ _ _ _

namespace Pb

def plogK {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (N : ℕ) (x : B) : B :=
  ∑ k ∈ Finset.range N, (-1) ^ k * (k.factorial : B) * δ.dpow (k + 1) x

section K
variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

structure CLiftK {C : Type 1} [Category.{0} C] (g : C ⥤ Thick (smFun X q)) (D : E.LineData X) where
  p : ∀ c : C, Spec (CommRingCat.of ((g.obj c).B ⧸ (g.obj c).J)) ⟶ D.Y
  hp : ∀ c : C, p c ≫ D.f = pt (g.obj c)
  w : ∀ {c c' : C}, (c ⟶ c') → (g.obj c').Bˣ
  hw : ∀ {c c' : C} (φ : c ⟶ c')
    (h : (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c').J (g.map φ).φ (g.map φ).hle)) ≫ p c) ≫ D.f = p c' ≫ D.f),
    Ideal.Quotient.mk (g.obj c').J (w φ) = (Scheme.ΓSpecIso (CommRingCat.of ((g.obj c').B ⧸ (g.obj c').J))).hom.hom
      (D.u (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (g.obj c').J (g.map φ).φ (g.map φ).hle)) ≫ p c) (p c') h)

def CLiftK.r {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X}
    (Λ : CLiftK g D) (s : ComposableArrows C 2) : (g.obj (s.obj (Fin.last 2))).Bˣ :=
  Units.map (g.map (s.map' 1 2)).φ.toMonoidHom (Λ.w (s.map' 0 1)) * Λ.w (s.map' 1 2) * (Λ.w (s.map' 0 2))⁻¹

variable (q) in

def IsFirstChernDeRham (D : E.LineData X) (x : HdR q 2) : Prop :=
  ∀ (s : ℕ) (C : Type 1) [Category.{0} C] (g : C ⥤ Thick (smFun X q)), (∀ c, (g.obj c).pdPow s = ⊥) →
    (∀ c, ∃ (V : X.Opens) (σ : (V : Scheme.{0}) ⟶ D.Y), σ ≫ D.f = V.ι ∧ InU V (g.obj c)) →
    ∀ Λ : CLiftK g D, ∃ (z : CH.Cn (g ⋙ O (smFun X q)) 2) (hz : CH.d _ 2 z = 0),
      (∀ σ : ComposableArrows C 2, (show (g.obj (σ.obj (Fin.last 2))).B from z σ) =
        plogK (g.obj (σ.obj (Fin.last 2))).δ s ((Λ.r σ : (g.obj (σ.obj (Fin.last 2))).B) - 1)) ∧
      (CH.cx _).cls z hz = (CH.Mor.restrict (O (smFun X q)) g).pull 2 x

end K

section O1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] MvPolynomial.gradedAlgebra

theorem X_mem (R : Type) [CommRing R] (N : ℕ) (j : Fin (N + 1)) :
    (MvPolynomial.X j : MvPolynomial (Fin (N + 1)) R) ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 1 :=
  MvPolynomial.isHomogeneous_X R j

abbrev ChartR (R : Type) [CommRing R] (N : ℕ) (j : Fin (N + 1)) : Type :=
  HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X j)

def chart (R : Type) [CommRing R] (N : ℕ) (j : Fin (N + 1)) : Spec (CommRingCat.of (ChartR R N j)) ⟶ PSpace R N :=
  Proj.awayι _ (MvPolynomial.X j) (X_mem R N j) one_pos

def ratio (R : Type) [CommRing R] (N : ℕ) (j k : Fin (N + 1)) : ChartR R N j :=
  HomogeneousLocalization.Away.mk _ (X_mem R N j) 1 (MvPolynomial.X k) (by simpa using X_mem R N k)

def IsTautologicalLineAt {R : Type} [CommRing R] {X : Scheme.{0}} (D : E.LineData X) (N : ℕ) (i : X ⟶ PSpace R N) : Prop :=
  Etale D.f ∧ ∃ s : ∀ j : Fin (N + 1), pullback i (chart R N j) ⟶ D.Y,
    ∃ hs : ∀ j, s j ≫ D.f = pullback.fst _ _,
    ∀ (V : Scheme.{0}) (j k : Fin (N + 1)) (a : V ⟶ pullback i (chart R N j)) (b : V ⟶ pullback i (chart R N k))
      (h : a ≫ pullback.fst _ _ = b ≫ pullback.fst _ _),
      ((D.u (a ≫ s j) (b ≫ s k) (by rw [Category.assoc, Category.assoc, hs, hs, h]) : (Γ(V, ⊤))ˣ) : Γ(V, ⊤)) =
        (a ≫ pullback.snd _ _).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (ChartR R N j))).inv.hom (ratio R N j k))

def IsTautologicalLine {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) (D : E.LineData X) : Prop :=
  ∃ (N : ℕ) (i : X ⟶ PSpace R N), IsClosedImmersion i ∧ i ≫ PSpace.str R N = p ∧ IsTautologicalLineAt D N i

end O1

end Pb

end CrystallineSemistableComparison
