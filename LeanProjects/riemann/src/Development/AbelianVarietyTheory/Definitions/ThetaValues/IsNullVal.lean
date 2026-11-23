import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaForm

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

abbrev LatMod (Dw : Datum H) (k : ℕ) : Type :=
  Dw.La ⧸ (Ideal.span {(k : 𝓞 E)} • ⊤ : Submodule (𝓞 E) Dw.La)

abbrev LevGrp (Dw : Datum H) (k : ℕ) : Type := LatMod Dw k ≃ₗ[𝓞 E] LatMod Dw k

variable (Xo : Moduli Dw l) (c : Coeff l)

def IsFullLev (k : ℕ) {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X)
    (ev : LatMod Dw k → (ptO Xo x0 ⟶ Xo.univ.t.G)) : Prop :=
  (∀ a b, ev (a + b) = ev a * ev b) ∧ (∀ (o : 𝓞 E) a, ev (o • a) = ev a ≫ Xo.univ.t.act.act o) ∧
    ∀ (K : Type) [Field K] (χ : S →+* K) (a b : LatMod Dw k),
      spMap χ ≫ (ev a).left = spMap χ ≫ (ev b).left → a = b

def IsNullVal (N : ℕ) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (p : ptO Xo y.x ⟶ Xo.univ.t.G) (w : S) : Prop :=
  ∃ F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x)),
    IsVtOver Xo.univ.t.G Xo.univ.t.PP N (fun t => t = p) y.s (p ^ N) F ∧
    IsValueAt Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) F 1
      (rigT Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (ptO Xo y.x) ((N : ℤ) ^ 2)) (toΓ S w)

def etaExpr {S : Type} [CommRing S] (k : ℕ) {J : Type} [Fintype J] {n : ℕ} (cf : J → ℤ)
    (x : J → Fin n → LatMod Dw k) (w : LatMod Dw k → S) : S :=
  ∏ᶠ g : LevGrp Dw k, ∑ j, (cf j : S) * ∏ b, w (g (x j b))

def EtaValAt (R : ℕ) {J : Type} [Fintype J] {n : ℕ} (cf : J → ℤ) (x : J → Fin n → LatMod Dw (R ^ 4))
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S) : Prop :=
  ∃ (S' : Type) (_ : CommRing S') (_ : Algebra c.F S') (φ : S →ₐ[c.F] S') (y' : FrPt Xo c S')
    (ev : LatMod Dw (R ^ 4) → (ptO Xo y'.x ⟶ Xo.univ.t.G)) (w : LatMod Dw (R ^ 4) → S'),
    φ.toRingHom.FaithfullyFlat ∧ FrMap φ y y' ∧ IsFullLev Xo (R ^ 4) y'.x ev ∧
    (∀ q, IsNullVal Xo c (R ^ 2) y' (ev q) (w q)) ∧ φ v = etaExpr (R ^ 4) cf x w

def IsEtaRule (R : ℕ) {J : Type} [Fintype J] {n : ℕ} (cf : J → ℤ) (x : J → Fin n → LatMod Dw (R ^ 4))
    (f : Rul Xo c) : Prop :=
  ∀ (p : TRing c.F) (y : FrPt Xo c p.R), EtaValAt Xo c R cf x y (f p y)

def shiftFam (R : ℕ) {n : ℕ} (x₀ : Fin n → Dw.La) (y : Fin n → LatMod Dw R) : Fin n → LatMod Dw (R ^ 4) :=
  fun b => Submodule.Quotient.mk (x₀ b + R • qRep (y b))

end GlobalTheory.EtaForm
