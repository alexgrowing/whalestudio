import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CurveFormSign

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def wVal (H : Host E) : ℂ := (1 + H.rt0) / 2

def rtSign (H : Host E) : ℤ := if 0 < H.rt0.im then 1 else -1

def wTyp (H : Host E) (ε : Bool) : 𝓞 E := if ε then H.w0 else H.bar H.w0

def pureVec {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P)
    (ε : Bool) : Submodule (𝓞 E) D.La where
  carrier := {v | ∀ i, ¬ (ty i (H.rt : E) = H.rt0 ↔ ε = true) → P v i = 0}
  zero_mem' i _ := by simp
  add_mem' {a b} ha hb i hi := by simp [ha i hi, hb i hi]
  smul_mem' a v hv i hi := by rw [hP.1, hv i hi, mul_zero]

def PureSpan {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) : Prop :=
  ∀ v : D.La, ∃ n : ℕ, 0 < n ∧ n • v ∈ pureVec hP true ⊔ pureVec hP false

def curveForm (H : Host E) (a b : ℂ) : ℝ := (a * starRingEnd ℂ b).im / (Real.sqrt H.d / 2)

def InCurveLat (H : Host E) (z : ℂ) : Prop := ∃ m n : ℤ, z = m + n * wVal H

def IsCurveUnif (H : Host E) {k : Type} [Field k] [Algebra k ℂ] (C : Out.PolAV (Sp k)) (wC : C.A ⟶ C.A)
    (e : ℂ → (Over.mk (spMap (algebraMap k ℂ)) ⟶ C.A)) : Prop :=
  (∀ z z', e (z + z') = e z * e z') ∧ Function.Surjective e ∧ (∀ z, e z = 1 ↔ InCurveLat H z) ∧
    (∀ z, e (wVal H * z) = e z ≫ wC) ∧ IsHolTo Set.univ (fun z => (e z).left) ∧
    ∀ (n : ℕ) (a b : ℂ) (c : ℂˣ), 0 < n → InCurveLat H a → InCurveLat H b →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (curveForm H a b : ℂ) / n) →
      Out.WeilIs C.A C.L n (e ((n : ℂ)⁻¹ * a)) (e ((n : ℂ)⁻¹ * b)) (unitOn c)

def polCoeffOne (D : Datum H) (v : D.La) (ε' : Bool) (v' : D.La) : ℤ := -(rtSign H * D.EF v (wTyp H ε' • v'))

def polCoeffW (D : Datum H) (v v' : D.La) : ℤ := rtSign H * D.EF v v'

section Maps

variable {S X Y : Scheme.{0}} (C : Over S) (G : Over X) (f : Y ⟶ S) (x : Y ⟶ X)

abbrev MapOver : Type := Over.mk (pullback.snd C.hom f ≫ x) ⟶ G

variable {C G f x}

def MapOver.ev (φ : MapOver C G f x) {T : Scheme.{0}} (t : T ⟶ Y) (p : Over.mk (t ≫ f) ⟶ C) :
    Over.mk (t ≫ x) ⟶ G :=
  Over.homMk (pullback.lift p.left t (Over.w p) ≫ φ.left) (by
    have := Over.w φ
    simp only [Over.mk_left, Over.mk_hom, Functor.id_obj, Functor.const_obj_obj] at this ⊢
    rw [Category.assoc, this, pullback.lift_snd_assoc])

end Maps

section Clauses

variable {S X Y : Scheme.{0}} {C : Over S} [GrpObj C] {G : Over X} [GrpObj G] {f : Y ⟶ S} {x : Y ⟶ X}

def MapOver.IsHom (φ : MapOver C G f x) : Prop :=
  ∀ (T : Scheme.{0}) (t : T ⟶ Y) (p q : Over.mk (t ≫ f) ⟶ C), φ.ev t (p * q) = φ.ev t p * φ.ev t q

def MapOver.Intertwines (φ : MapOver C G f x) (a : C ⟶ C) (b : G ⟶ G) : Prop :=
  ∀ (T : Scheme.{0}) (t : T ⟶ Y) (p : Over.mk (t ≫ f) ⟶ C), φ.ev t (p ≫ a) = φ.ev t p ≫ b

def MapOver.PolIdentity (φ ψ : MapOver C G f x) (LC : LB C.left) (LG : LB G.left) (w : C ⟶ C) (m n : ℤ) : Prop :=
  ∀ (T : Scheme.{0}) (t : T ⟶ Y) (N : ℕ) (p q : Over.mk (t ≫ f) ⟶ C) (c : Γ(T, ⊤)ˣ), 0 < N → p ^ N = 1 → q ^ N = 1 →
    Out.WeilIs C LC N (T := Over.mk (t ≫ f)) (p ^ m * (p ≫ w) ^ n) q c →
    Out.WeilIs G LG N (T := Over.mk (t ≫ x)) (φ.ev t p) (ψ.ev t q) c

def GenerateFibres {J : Type} (φ : J → MapOver C G f x) : Prop :=
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Y),
    Subgroup.closure {y : Over.mk (t ≫ x) ⟶ G | ∃ (j : J) (p : Over.mk (t ≫ f) ⟶ C), y = (φ j).ev t p} = ⊤

end Clauses

def IsSpread {D₀ : Datum H} {l : Level H} {Xo : Moduli D₀ l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (U : FamilyUnif Xo σ ty) (i : Fin U.n) {P : (U.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (U.Di i) ty P)
    {k : Type} [Field k] [Algebra k ℂ] (C : Out.PolAV (Sp k)) (wC : C.A ⟶ C.A)
    (e : ℂ → (Over.mk (spMap (algebraMap k ℂ)) ⟶ C.A)) {Y : Scheme.{0}} (f : Y ⟶ Sp k) (s : Sp ℂ ⟶ Y) (x : Y ⟶ Xo.X)
    (φ : ∀ ε : Bool, pureVec hP ε → MapOver C.A Xo.univ.t.G f x) : Prop :=
  s ≫ x = U.u i P ∧
  (∀ (ε : Bool) (v : pureVec hP ε), (φ ε v).IsHom) ∧
  (∀ (ε : Bool) (v v' : pureVec hP ε), φ ε (v + v') = φ ε v * φ ε v') ∧
  (∀ (ε : Bool) (a : 𝓞 E) (v : pureVec hP ε), φ ε (a • v) = φ ε v ≫ Xo.univ.t.act.act a) ∧
  (∀ (ε : Bool) (v : pureVec hP ε), (φ ε v).Intertwines wC (Xo.univ.t.act.act (wTyp H ε))) ∧
  (∀ (ε ε' : Bool) (v : pureVec hP ε) (v' : pureVec hP ε'),
    (φ ε v).PolIdentity (φ ε' v') C.L Xo.univ.t.PP.L wC (polCoeffOne (U.Di i) v.1 ε' v'.1)
      (polCoeffW (U.Di i) v.1 v'.1)) ∧
  GenerateFibres (fun j : (Σ ε : Bool, pureVec hP ε) => φ j.1 j.2) ∧
  ∀ (ε : Bool) (v : pureVec hP ε) (z : ℂ) (p : Over.mk (s ≫ f) ⟶ C.A), p.left = (e z).left →
    ((φ ε v).ev s p).left = (U.ex i P (z • P v.1)).left

def CMPointSpread : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D₀ : Datum H) (l : Level H) (Xo : Moduli D₀ l)
    (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty) (i : Fin U.n)
    (P : (U.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (U.Di i) ty P), PureSpan hP →
    ∀ (k : Type) [Field k] [NumberField k] [Algebra k ℂ] (C : Out.PolAV (Sp k)) (wC : C.A ⟶ C.A)
      (e : ℂ → (Over.mk (spMap (algebraMap k ℂ)) ⟶ C.A)), C.g = 1 → IsMonHom wC → IsCurveUnif H C wC e →
      ∃ (R : Subalgebra k ℂ) (x : Sp R ⟶ Xo.X)
        (φ : ∀ ε : Bool, pureVec hP ε → MapOver C.A Xo.univ.t.G (spMap (algebraMap k R)) x),
        R.FG ∧ IsSpread U i hP C wC e (spMap (algebraMap k R)) (spMap (algebraMap R ℂ)) x φ

end GlobalTheory.IndefiniteRowSideFullHecke.CurveFormSign
