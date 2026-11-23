import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

attribute [local instance] Over.cartesianMonoidalCategory

namespace MainStatements.Hodge

def IsPullbackH2Structure {R R' : Type} [CommRing R] [CommRing R'] {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'}
    {σ : R →+* R'} {φ : X' ⟶ X} (h : φ ≫ s = s' ≫ spMap σ) (c : GlobalTheory.CatCoh.H2 (OAff s)) (c' : GlobalTheory.CatCoh.H2 (OAff s')) : Prop :=
  (pairPull h).pull2 c = (pairRes φ s').pull2 c'

def HopfLeSt : Prop := AllFin fun R _ _ _ F ↦ ∀ g : ℕ, IsField R → Stein F →
  (∀ n, g ≤ n → Function.Exact (dn F n) (dn F (n + 1))) → Hopf F True →
  ∀ x : Fin (g + 1) → GlobalTheory.CatCoh.H1 F, ¬ LinearIndependent R x

def H1StructureFieldDim : Prop := AllAb fun R _ A _ g ↦ IsField R → VB R (HO1 A.hom) g

def NoPrimSt : Prop := AllAb fun R _ A _ _ ↦ IsField R →
  ∀ (z : GlobalTheory.CatCoh.H2 (OAff A.hom)) (a b c : GlobalTheory.CatCoh.H2 (OAff (A ⊗ A).hom)),
    IsPullbackH2Structure (wOver (fst A A * snd A A)) z a → IsPullbackH2Structure (wOver (fst A A)) z b → IsPullbackH2Structure (wOver (snd A A)) z c →
    a = b + c → z = 0

def SmallLiftSt : Prop := AllAb fun R _ A _ _ ↦ ∀ [IsLocalRing R] (t : R), (∀ x, ¬ IsUnit x → x * t = 0) →
  ∀ (X' : Scheme.{0}) (s' : X' ⟶ Sp (R ⧸ Ideal.span {t})) (φ : X' ⟶ A.left)
    (h : IsPullback φ s' A.hom (spMap (algebraMap R (R ⧸ Ideal.span {t})))) (c' : HO1 s'),
    ∃ c : HO1 A.hom, IsPullO h.w c c'

def PerfVBSt : Prop := AllFin fun R _ C _ F ↦ ∀ g : ℕ, Perf F → SteinU F →
  (∀ (k : Type) [Field k] [Algebra R k], ∃ (F' : C ⥤ CommAlgCat.{0} k) (_ : BC F F'),
    Module.finrank k (GlobalTheory.CatCoh.H1 F') = g) →
  (∀ (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B] (t : B), (∀ x, ¬ IsUnit x → x * t = 0) →
    ∃ (F' : C ⥤ CommAlgCat.{0} B) (_ : BC F F') (F'' : C ⥤ CommAlgCat.{0} (B ⧸ Ideal.span {t})) (m : BC F' F''),
      Function.Surjective m.coef.pull1) → VB R (GlobalTheory.CatCoh.H1 F) g

end MainStatements.Hodge
