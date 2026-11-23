import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.IsOpenPart
import Formalism.LocalToGlobal.ProjectiveLattices.EmbKCoe

noncomputable section

namespace Formalism.L2.Pj.PointsOfFlagModel

open AlgebraicGeometry CategoryTheory Limits MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.MainNotions.DIV.Cons (SCF intO)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

inductive MdlC : Type
  | xm : MdlC
  | yy : MdlC
  | xn : ℕ → MdlC

section PtC

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

structure PtC {p : ℕ} (Y : Model Xo c β) (C : SCF p) where
  alg : O →+* intO ↥C.S
  fK : c.F →+* ↥C.S
  compat : (intO ↥C.S).subtype.comp alg = fK.comp β
  y : Sp ↥C.S ⟶ Xo.XF c
  y_over : y ≫ pullback.snd _ _ = spMap fK
  yt : Sp ↥(intO ↥C.S) ⟶ Y.X
  yt_over : yt ≫ Y.s = spMap alg
  ext : spMap (intO ↥C.S).subtype ≫ yt = y ≫ Y.j

namespace PtC

variable {p : ℕ} {Y : Model Xo c β} {C : SCF p} (P : PtC Y C)

def x0 : Sp ↥C.S ⟶ Y.X := P.y ≫ Y.j

abbrev base : Over Y.X := Over.mk P.x0

abbrev epsB : Over Y.X := Over.mk (spMap (algebraMap ↥C.S (DualNumber ↥C.S)) ≫ P.x0)

def IsTan (v : P.epsB ⟶ Y.t.G) : Prop :=
  spMap (TrivSqZeroExt.fstHom ↥C.S ↥C.S ↥C.S).toRingHom ≫ v.left = (1 : P.base ⟶ Y.t.G).left

def emb (τ : E →+* ℂ) (a : 𝓞 E) : ↥C.S := P.fK ⟨τ (a : E), c.conj τ a⟩

def IsEig (τ : E →+* ℂ) (v : P.epsB ⟶ Y.t.G) : Prop :=
  ∀ a : 𝓞 E, (v ≫ Y.t.act.act a).left = spMap (epsMul (P.emb τ a)) ≫ v.left

def IsComb {m : ℕ} (v : Fin m → (P.epsB ⟶ Y.t.G)) (a : Fin m → ↥C.S) (w : P.epsB ⟶ Y.t.G) : Prop :=
  ∃ u : Fin m → (P.epsB ⟶ Y.t.G), (∀ i, (u i).left = spMap (epsMul (a i)) ≫ (v i).left) ∧ w = (List.ofFn u).prod

structure Flag where
  u : ∀ τ : E →+* ℂ, Fin (D.mult τ) → (P.epsB ⟶ Y.t.G)
  tan : ∀ τ i, P.IsTan (u τ i)
  eig : ∀ τ i, P.IsEig τ (u τ i)
  basis : ∀ τ (w : P.epsB ⟶ Y.t.G), P.IsTan w → P.IsEig τ w →
    ∃! a : Fin (D.mult τ) → ↥C.S, P.IsComb (u τ) a w

end PtC

end PtC

section Tower

variable {D : Datum H} {l : Level H}

abbrev abelian₂ (p : ℕ) (c : Coeff l) : Type :=
  {v : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F) // (p : 𝓞 c.F) ∈ v.asIdeal}

def BaseAt {c : Coeff l} (v : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F)) {O : Type} [CommRing O] (β : O →+* c.F) :
    Prop :=
  Function.Injective β ∧ ∀ x : c.F, x ∈ Set.range β ↔ v.valuation c.F x ≤ 1

structure Tower (p : ℕ) (Xo : Moduli D l) (c : Coeff l) where
  O : abelian₂ p c → Type
  [ring : ∀ v, CommRing (O v)]
  β : ∀ v, O v →+* c.F
  Y : ∀ v, Model Xo c (β v)
  lvN : ℕ → Level H
  XoN : ∀ n, Moduli D (lvN n)
  cN : ∀ n, Coeff (lvN n)
  ON : ∀ n, abelian₂ p (cN n) → Type
  [ringN : ∀ n w, CommRing (ON n w)]
  βN : ∀ n w, ON n w →+* (cN n).F
  YN : ∀ n w, Model (XoN n) (cN n) (βN n w)

attribute [instance] Tower.ring Tower.ringN

def TowerAt {p : ℕ} {Xo : Moduli D l} {c : Coeff l} (T : Tower p Xo c) : Prop :=
  (∀ v, BaseAt v.1 (T.β v) ∧ Nonempty (T.Y v).X) ∧
  ∀ n, l.Dvd (T.lvN n) ∧ p ^ n * l.A ∣ (T.lvN n).A ∧
    ∀ w, (BaseAt w.1 (T.βN n w) ∧ Nonempty (T.YN n w).X) ∧
      ∃ (v : abelian₂ p c) (bm : T.O v →+* T.ON n w) (π : (T.YN n w).X ⟶ (T.Y v).X), IsTransition (T.Y v) (T.YN n w) bm π

structure AtLevel (p : ℕ) (D : Datum H) where
  lv : Level H
  Xo : Moduli D lv
  c : Coeff lv
  T : Tower p Xo c

def ModelsAt (p : ℕ) (Xo : Moduli D l) (c : Coeff l) : Prop :=
  Nonempty {A : AtLevel p D // l.Dvd A.lv ∧ A.lv.GoodAt p ∧ TowerAt A.T ∧
    (l.GoodAt p → ∃ _ : A.lv = l, HEq A.Xo Xo ∧ HEq A.c c)}

def towerOf {p : ℕ} {Xo : Moduli D l} {c : Coeff l} (h : ModelsAt p Xo c) : AtLevel p D :=
  (Classical.choice h).1

theorem towerOf_at {p : ℕ} {Xo : Moduli D l} {c : Coeff l} (h : ModelsAt p Xo c) : TowerAt (towerOf h).T :=
  (Classical.choice h).2.2.2.1

end Tower

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l}

def Pt {p : ℕ} (T : Tower p Xo c) : MdlC → Type
  | .xm => Σ v : abelian₂ p c, Σ C : SCF p, PtC (T.Y v) C
  | .yy => Σ v : abelian₂ p c, Σ C : SCF p, Σ P : PtC (T.Y v) C, P.Flag
  | .xn n => Σ w : abelian₂ p (T.cN n), Σ C : SCF p, PtC (T.YN n w) C

def fld {p : ℕ} {T : Tower p Xo c} : ∀ {Z : MdlC}, Pt T Z → Formalism.MainNotions.ModuliIntegralCharts.CF p
  | .xm, y => y.2.1.toCF
  | .yy, y => y.2.1.toCF
  | .xn _, y => y.2.1.toCF

def toXm {p : ℕ} {T : Tower p Xo c} (y : Pt T .yy) : Pt T .xm := ⟨y.1, y.2.1, y.2.2.1⟩

theorem fld_toXm {p : ℕ} {T : Tower p Xo c} (y : Pt T .yy) : fld (toXm y) = fld y := rfl

end Formalism.L2.Pj.PointsOfFlagModel
