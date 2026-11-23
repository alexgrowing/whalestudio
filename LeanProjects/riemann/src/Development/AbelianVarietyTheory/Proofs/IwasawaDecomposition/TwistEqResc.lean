import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CoeffSpecAlgebraMapOfNeg
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM GlobalTheory.LocM.FJ GlobalTheory.Toroidal GlobalTheory.Ex
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Ex.NumD

variable {O : Type} [CommRing O] (N : NumD O)

def resc (h : N.X → Oˣ) (t : N.X → N.X → Oˣ) (h_add : ∀ x y, h (x + y) = h x * h y * t x y) (h_neg : ∀ x, h (-x) = h x)
    (t_add : ∀ x x' y, t (x + x') y = t x y * t x' y) : NumD O :=
  { N with ψ := fun χ => N.ψ χ * h χ
           even := fun χ => by rw [h_neg, mul_right_comm, N.even χ]
           bimult := fun a a' b => by
             have e : ∀ x y : N.X, N.ψ (x + y) * h (x + y) / (N.ψ x * h x) / (N.ψ y * h y) =
                 N.ψ (x + y) / N.ψ x / N.ψ y * t x y := fun x y => by
               rw [h_add]
               apply Additive.ofMul.injective
               simp only [ofMul_mul, ofMul_div]; abel
             rw [e, e, e, mul_right_comm, N.bimult a a' b, t_add]
             exact mul_mul_mul_comm _ _ _ _ }

end GlobalTheory.Ex.NumD

namespace GlobalTheory.LocM.MultiPt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

section Terms

variable {R : Type} [CommRing R] [IsDomain R] {C : Type} [Field C] [Algebra (FractionRing R) C] (A : ArcF D R C)

def vec (m : ℕ) (x : D.La) (χ : A.N.X) : A.D₀.X := A.ν.eX ((A.q (m ^ 2) x).1.1.toAdd + m • χ)

def txR (Q : ℕ → A.D₀.X → Cˣ) (m : ℕ) (x : D.La) (χ : A.N.X) : C :=
  (Q (m ^ 2) (vec A m x χ) : C) * A.N.txT m (A.q (m ^ 2) x) χ

def evR (Q : ℕ → A.D₀.X → Cˣ) (T : ℕ → A.D₀.X → A.D₀.X → Cˣ) (m j : ℕ) (z x : D.La) (χ : A.N.X) : C :=
  ((Q (m ^ 2) (vec A m x χ) * T j (A.ν.eX (A.q j z).1.1.toAdd) (vec A m x χ) : Cˣ) : C) *
    A.N.evT m (A.q (m ^ 2) x) (A.q j z).1.2 χ

end Terms

def GReal {R : Type} [CommRing R] [IsDomain R] {C : Type} [NormedField C] [Algebra (FractionRing R) C] (o : Full D C)
    (A : ArcF D R C) (Q : ℕ → A.D₀.X → Cˣ) (T : ℕ → A.D₀.X → A.D₀.X → Cˣ) : Prop :=
  o.ρ = A.ρ ∧ (∀ n, 0 < n → o.I.ζ n = A.I.ζ n) ∧ ∀ m, Odd m → o.Theta m (fun x => ∑' χ, txR A Q m x χ) ∧
    ∀ j, 0 < j → ∀ z, o.Coord m (o.I.ev j z) fun x => ∑' χ, evR A Q T m j z x χ

def mQ {X : Type} [AddCommGroup X] {C : Type} [Field C] {r : ℕ} (δ : Fin r → LinearMap.BilinForm ℤ X) (ρ : Fin r → ℕ → Cˣ)
    (n : ℕ) (w : X) : Cˣ := ∏ i, ρ i n ^ (δ i w w / 2)

def mT {X : Type} [AddCommGroup X] {C : Type} [Field C] {r : ℕ} (δ : Fin r → LinearMap.BilinForm ℤ X) (ρ : Fin r → ℕ → Cˣ)
    (n : ℕ) (y w : X) : Cˣ := ∏ i, ρ i n ^ δ i y w

variable {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def HasPt (Y : Model Xo c β) (m : ℕ) {κ : Type} [Field κ] (x : Sp κ ⟶ Xo.XF c) (ζ : κ) (v : D.La → κ)
    (w : D.La → D.La → κ) : Prop :=
  ∃ (Ω : Type) (_ : Field Ω) (f : κ →+* Ω) (o : Full D Ω), FullAt Y (spMap f ≫ x) o ∧ (o.I.ζ (m ^ 2) : Ω) = f ζ ∧
    o.Theta m (fun a => f (v a)) ∧ ∀ z, o.Coord m (o.I.ev l.M' z) fun a => f (w z a)

def reform {A₀ : Type} [CommRing A₀] [IsDomain A₀] {b : O →+* A₀} {a : ArcIn D l β A₀ b} {F : Type} [Field F]
    [Algebra (FractionRing A₀) F] (A : Lift a F) (ga : levelForms H l.M' a.D₀.X) (h : ga ∈ admitted H l.M' a.D₀.X) :
    Lift (withForm a ga h) F :=
  { A with
    be := { be := ga.1.comp A.ν.eX.toIntLinearEquiv.toLinearMap A.ν.eX.toIntLinearEquiv.toLinearMap
            symm := fun _ _ => ga.2.1 _ _
            pos := fun y hy => h.1 _ ((map_ne_zero_iff _ A.ν.eX.injective).2 hy)
            dvd := fun _ _ => h.2 _ _ }
    be_eq := fun _ _ => rfl }

end GlobalTheory.LocM.MultiPt

end
