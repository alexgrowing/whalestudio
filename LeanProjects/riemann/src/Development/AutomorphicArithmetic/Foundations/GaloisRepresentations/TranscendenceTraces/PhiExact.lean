import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PhiSecRes

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace UpperTheory.Gal.TranscendenceTraces

def PhiUniv : Prop := ∀ (Q : ℕ) {Z S : Scheme.{0}} (p : Z ⟶ S) (G J : Shv (ZMod Q)) (t : Fam0 p G J),
  ∃! m : (phi p (ZMod Q)).obj G ⟶ J, ∀ A a, Sec.map m ((phiE p G).app A a) = t.app A a

def DSOne : Prop := ∀ (R : Type) [CommRing R] {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (T : ShortComplex (Shv R)), T.Exact →
  ∀ (U : Scheme.{0}) (u : U ⟶ S) (b : Sec T.X₂ (pullback p u)), Sec.map T.g b = 0 →
  Loc U fun V g => ∃ a : DS p T.X₁ V, DS.map p T.f V a = DS.res p T.X₂ g (inc p T.X₂ u b)

def DSLoc : Prop := ∀ (R : Type) [CommRing R] {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (T : ShortComplex (Shv R)), T.Exact →
  ∀ (U : Scheme.{0}) (x : DS p T.X₂ U), DS.map p T.g U x = 0 →
  Loc U fun V g => ∃ a : DS p T.X₁ V, DS.map p T.f V a = DS.res p T.X₂ g x

def PhiExact : Prop := ∀ (R : Type) [CommRing R] {Z S : Scheme.{0}} (p : Z ⟶ S) [IsFinite p] (T : ShortComplex (Shv R)),
  T.Exact → (T.map (phi p R)).Exact

def PhiQis : Prop := ∀ (R : Type) [CommRing R] (Φ : Shv R ⥤ Shv R) [Φ.Additive],
  (∀ T : ShortComplex (Shv R), T.Exact → (T.map Φ).Exact) → ∀ F : Shv R,
  ∃ ε : sgl (Φ.obj F) ⟶ (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj (res R F), QuasiIso ε ∧
    sglι (Φ.obj F) ≫ ε.f 0 = Φ.map (resι R F)

def ExtRes : Prop := ∀ (R : Type) [CommRing R] (F G : Shv R) (T : Cx R) (ε : sgl F ⟶ T) [QuasiIso ε],
  (∀ a : F ⟶ G, ∃ m : T ⟶ res R G, sglι F ≫ ε.f 0 ≫ m.f 0 = a ≫ resι R G) ∧
  ∀ m m' : T ⟶ res R G, sglι F ≫ ε.f 0 ≫ m.f 0 = sglι F ≫ ε.f 0 ≫ m'.f 0 → ∀ (U : Scheme.{0}) (i n k : ℤ), i + 1 = n → n + 1 = k →
    ∀ y : Sec (T.X n) U, Sec.map (T.d n k) y = 0 → ∃ c, Sec.map ((res R G).d i n) c = Sec.map (m.f n) y - Sec.map (m'.f n) y

def FamHom : Prop := ∀ (Q : ℕ) {Z S : Scheme.{0}} (p : Z ⟶ S) (Φ : Shv (ZMod Q) ⥤ Shv (ZMod Q)) [Φ.Additive]
  (e : ∀ G, Fam0 p G (Φ.obj G)), Rep0 p Q Φ e → ∀ I J : Cx (ZMod Q),
  (∀ m : (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J, ∃ τ : Fam p I J,
    ∀ n A a, (τ.deg n).app A a = Sec.map (F := Φ.obj (I.X n)) (m.f n) ((e (I.X n)).app A a)) ∧
  ∀ τ : Fam p I J, ∃ m : (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J,
    ∀ n A a, (τ.deg n).app A a = Sec.map (F := Φ.obj (I.X n)) (m.f n) ((e (I.X n)).app A a)

end UpperTheory.Gal.TranscendenceTraces

end
