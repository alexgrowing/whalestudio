import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace UpperTheory.Gal.TranscendenceTraces

abbrev gp (Ω : Type) [Field Ω] : Scheme.{0} := Spec (CommRingCat.of Ω)

def pt {Ω : Type} [Field Ω] {X : Scheme.{0}} (x : gp Ω ⟶ X) : X := x (IsLocalRing.closedPoint Ω)

abbrev Wt (Z : Scheme.{0}) : Type 1 := ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω], (gp Ω ⟶ Z) → ℤ

def fib {Ω : Type} [Field Ω] {V U : Scheme.{0}} (r : V ⟶ U) (x : gp Ω ⟶ U) : Set (gp Ω ⟶ V) := {z | z ≫ r = x}

def Wt.comap {Z' Z : Scheme.{0}} (v : Z' ⟶ Z) (w : Wt Z) : Wt Z' := fun Ω _ _ z => w Ω (z ≫ v)

def Wt.push {Z Z' : Scheme.{0}} (h : Z ⟶ Z') (w : Wt Z) : Wt Z' := fun Ω _ _ x => ∑ᶠ z ∈ fib h x, w Ω z

def Wt.mul {W Z : Scheme.{0}} (r : W ⟶ Z) (w' : Wt W) (w : Wt Z) : Wt W := fun Ω _ _ z => w' Ω z * w Ω (z ≫ r)

def Wt.const (Z : Scheme.{0}) (d : ℤ) : Wt Z := fun _ _ _ _ => d

def Wt.add {Z : Scheme.{0}} (w w' : Wt Z) : Wt Z := fun Ω _ _ z => w Ω z + w' Ω z

def Wt.smul {Z : Scheme.{0}} (d : ℤ) (w : Wt Z) : Wt Z := fun Ω _ _ z => d * w Ω z

def mult {Z S : Scheme.{0}} (p : Z ⟶ S) : Wt Z := fun _ _ _ z =>
  ((Module.length ((pullback p (z ≫ p)).presheaf.stalk (pt (pullback.lift z (𝟙 _) (Category.id_comp _).symm)))
    ((pullback p (z ≫ p)).presheaf.stalk (pt (pullback.lift z (𝟙 _) (Category.id_comp _).symm)))).toNat : ℤ)

structure Sq {Z S : Scheme.{0}} (p : Z ⟶ S) : Type 1 where
  U : Scheme.{0}
  V : Scheme.{0}
  u : U ⟶ S
  v : V ⟶ Z
  r : V ⟶ U
  pb : IsPullback v r p u

def Sq.of {Z S U : Scheme.{0}} (p : Z ⟶ S) (u : U ⟶ S) : Sq p :=
  ⟨U, pullback p u, u, pullback.fst p u, pullback.snd p u, IsPullback.of_hasPullback p u⟩

def Sq.self {Z S : Scheme.{0}} (p : Z ⟶ S) : Sq p := ⟨S, Z, 𝟙 S, 𝟙 Z, p, IsPullback.of_horiz_isIso ⟨by simp⟩⟩

structure Sq.To {Z S : Scheme.{0}} {p : Z ⟶ S} (A B : Sq p) where
  g : A.U ⟶ B.U
  k : A.V ⟶ B.V
  hu : g ≫ B.u = A.u
  hv : k ≫ B.v = A.v
  hr : k ≫ B.r = A.r ≫ g

def IsWt {Z S : Scheme.{0}} (p : Z ⟶ S) (w : Wt Z) : Prop :=
  ∀ (A : Sq p) (φ : A.V → ℤ), IsLocallyConstant φ → ∃ ψ : A.U → ℤ, IsLocallyConstant ψ ∧
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : gp Ω ⟶ A.U), ψ (pt x) = ∑ᶠ z ∈ fib A.r x, w Ω (z ≫ A.v) * φ (pt z)

theorem isWt_zero {Z S : Scheme.{0}} (p : Z ⟶ S) : IsWt p (Wt.const Z 0) := fun _ _ _ =>
  ⟨0, IsLocallyConstant.const 0, fun _ _ _ _ => by simp [Wt.const]⟩

def IsSum {R : Type} [CommRing R] {F : Shv R} {Z S : Scheme.{0}} {p : Z ⟶ S} (w : Wt Z) (A : Sq p) (a : Sec F A.V)
    (b : Sec F A.U) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : gp Ω ⟶ A.U), Sec.res x b = ∑ᶠ z ∈ fib A.r x, w Ω (z ≫ A.v) • Sec.res z a

structure Fam0 {Z S : Scheme.{0}} (p : Z ⟶ S) {R' R : Type} [CommRing R'] [CommRing R] (F : Shv R') (G : Shv R) where
  app : ∀ A : Sq p, Sec F A.V →+ Sec G A.U
  nat : ∀ {A B : Sq p} (t : A.To B) (a : Sec F B.V), Sec.res t.g (app B a) = app A (Sec.res t.k a)

instance {Z S : Scheme.{0}} (p : Z ⟶ S) {R' R : Type} [CommRing R'] [CommRing R] (F : Shv R') (G : Shv R) :
    Zero (Fam0 p F G) := ⟨⟨fun _ => 0, fun _ _ => by simp⟩⟩

structure Fam {Z S : Scheme.{0}} (p : Z ⟶ S) {R' R : Type} [CommRing R'] [CommRing R] (I : Cx R') (J : Cx R) where
  deg : ∀ s : ℤ, Fam0 p (I.X s) (J.X s)
  comm : ∀ (A : Sq p) (s t : ℤ) (a : Sec (I.X s) A.V),
    Sec.map (J.d s t) ((deg s).app A a) = (deg t).app A (Sec.map (I.d s t) a)

instance {Z S : Scheme.{0}} (p : Z ⟶ S) {R' R : Type} [CommRing R'] [CommRing R] (I : Cx R') (J : Cx R) :
    Zero (Fam p I J) := ⟨⟨fun _ => 0, fun _ _ _ _ => map_zero _⟩⟩

def Fam.Over {Z S : Scheme.{0}} {p : Z ⟶ S} {R' R : Type} [CommRing R'] [CommRing R] {F : Shv R'} {G : Shv R}
    (τ : Fam p (res R' F) (res R G)) (t : Fam0 p F G) : Prop :=
  ∀ (A : Sq p) (a : Sec F A.V), (τ.deg 0).app A (Sec.map (resι R' F) a) = Sec.map (resι R G) (t.app A a)

def Fam.IsImage {Z S : Scheme.{0}} {p : Z ⟶ S} {R' R : Type} [CommRing R'] [CommRing R] {I : Cx R'} {J : Cx R}
    (τ : Fam p I J) {n : ℤ} (α : Cochain ((chains R').obj (sch.obj Z)) I n) (β : Cochain ((chains R).obj (sch.obj S)) J n) :
    Prop :=
  ∀ (k : ℕ) (s : ℤ) (h : -(k : ℤ) + n = s) (A : Sq p), ev β k s h A.U A.u = (τ.deg s).app A (ev α k s h A.V A.v)

def Fam.op {Z S : Scheme.{0}} {p : Z ⟶ S} {R' R : Type} [CommRing R'] [CommRing R] {I : Cx R'} {J : Cx R} (τ : Fam p I J)
    (n : ℤ) : CohomologyClass ((chains R').obj (sch.obj Z)) I n →+ CohomologyClass ((chains R).obj (sch.obj S)) J n :=
  pick fun c => ∀ (α : Cocycle _ I n) (β : Cocycle _ J n), τ.IsImage α.1 β.1 →
    c (CohomologyClass.mk α) = CohomologyClass.mk β

def tr0 {Z S : Scheme.{0}} (p : Z ⟶ S) (w : Wt Z) (q : ℕ) (i : ℤ) : Fam0 p (tw q i) (tw q i) :=
  pick fun t => ∀ (A : Sq p) (a : Sec (tw q i) A.V), IsSum w A a (t.app A a)

def trFam {Z S : Scheme.{0}} (p : Z ⟶ S) (w : Wt Z) (q : ℕ) (i : ℤ) : Fam p (res _ (tw q i)) (res _ (tw q i)) :=
  pick fun τ => τ.Over (tr0 p w q i)

def tr {Z S : Scheme.{0}} (p : Z ⟶ S) (w : Wt Z) (q : ℕ) (n i : ℤ) : Ht q (sch.obj Z) n i →+ Ht q (sch.obj S) n i :=
  (trFam p w q i).op n

def trHl (l : ℕ) [Fact l.Prime] {Z S : Scheme.{0}} (p : Z ⟶ S) (w : Wt Z) (n i : ℤ) :
    Hl l (sch.obj Z) n i →ₗ[ℤ_[l]] Hl l (sch.obj S) n i :=
  pick fun T => ∀ (x : Hl l (sch.obj Z) n i) (k : ℕ), (T x).1 k = tr p w (l ^ k) n i (x.1 k)

def trHQ (l : ℕ) [Fact l.Prime] {Z S : Scheme.{0}} (p : Z ⟶ S) (w : Wt Z) (n i : ℤ) :
    HQ l (sch.obj Z) n i →ₗ[ℚ_[l]] HQ l (sch.obj S) n i := (trHl l p w n i).baseChange ℚ_[l]

structure Corr (S Y : Scheme.{0}) : Type 1 where
  Z : Scheme.{0}
  p : Z ⟶ S
  f : Z ⟶ Y
  w : Wt Z
  fin : IsFinite p
  wt : IsWt p w

def Corr.zero {S Y : Scheme.{0}} (f : S ⟶ Y) : Corr S Y := ⟨S, 𝟙 S, f, Wt.const S 0, inferInstance, isWt_zero _⟩

def Corr.cyc {S Y : Scheme.{0}} (c : Corr S Y) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : gp Ω ⟶ S) (y : gp Ω ⟶ Y) : ℤ :=
  ∑ᶠ z ∈ {z : gp Ω ⟶ c.Z | z ≫ c.p = x ∧ z ≫ c.f = y}, c.w Ω z

def Corr.op {S Y : Scheme.{0}} (c : Corr S Y) (q : ℕ) (n i : ℤ) : Ht q (sch.obj Y) n i →+ Ht q (sch.obj S) n i :=
  (tr c.p c.w q n i).comp (pull _ (sch.map c.f) _ n)

def Corr.opQ (l : ℕ) [Fact l.Prime] {S Y : Scheme.{0}} (c : Corr S Y) (n i : ℤ) :
    HQ l (sch.obj Y) n i →ₗ[ℚ_[l]] HQ l (sch.obj S) n i :=
  (trHQ l c.p c.w n i).comp (pullHQ l (sch.map c.f) n i)

def Nml (S : Scheme.{0}) : Prop := ∀ s : S, IsDomain (S.presheaf.stalk s) ∧ IsIntegrallyClosed (S.presheaf.stalk s)

end UpperTheory.Gal.TranscendenceTraces

end
