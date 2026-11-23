import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BlockTh

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

structure Bk (Dw : Datum H) (n : ℕ) where
  τ : E →+* ℂ
  i : ℕ
  hi : i ≤ Dw.mult τ
  c : ℕ
  hc : 1 ≤ c
  col : Fin i → Fin n
  col_inj : Function.Injective col

variable {Dw : Datum H} {n : ℕ}

def Bk.poly (K : Type) [CommRing K] (B : Bk Dw n) : MvPolynomial (LtN Dw n) K :=
  (Matrix.of fun a b : Fin B.i => MvPolynomial.X (⟨B.τ, Fin.castLE B.hi a, B.col b⟩ : LtN Dw n)).det ^ B.c

def IsBlockProd {K : Type} [CommRing K] (P : MvPolynomial (LtN Dw n) K) : Prop :=
  ∃ (nb : ℕ) (bs : Fin nb → Bk Dw n), (∀ j j', j ≠ j' → ∀ a a', (bs j).col a ≠ (bs j').col a') ∧
    P = ∏ j, (bs j).poly K

variable {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)

def ContainsTh (nab : NabV Xo c) (s : c.F) (P : MvPolynomial (LtN Dw n) c.F) {J : Type} (w : J → Rul Xo c) : Prop :=
  ∃ jb : (Fin n → LevQ Dw l) → J, Function.Injective jb ∧
    ∀ q, ∃ f : Rul Xo c, IsThRule Xo c nab (fun b => levRep (q b)) P f ∧ ∀ (p : TRing c.F) (y : FrPt Xo c p.R), w (jb q) p y = algebraMap c.F p.R s * f p y

variable (E) in

def p14 (r n m : ℕ) : ℝ :=
  (Real.log Real.pi + n * (Real.log 24 + (I2.dstar (E := E) m : ℝ) / 2 * Real.log (2 * (I2.dstar (E := E) m : ℝ))) +
    (r + 2) * Real.log 2) / 2

end GlobalTheory.BlockTh
