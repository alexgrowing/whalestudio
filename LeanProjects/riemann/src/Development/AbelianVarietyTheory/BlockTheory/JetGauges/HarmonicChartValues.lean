import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.HarmonicSystemChartValues

open AlgebraicGeometry CategoryTheory NumberField
open Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

abbrev SecAt {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (k : ℕ) : Type :=
  LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L (k : ℤ) (ptO Xo y.x))

def colSum {S : Type} [CommRing S] [Algebra c.F S] {n : ℕ} (v : Fin n → (Lt1 Dw →₀ ℕ) → S)
    (P : MvPolynomial (LtN Dw n) c.F) : S :=
  ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b : Fin n, v b (colOf m b)

def chartVal [StarRing (𝓞 E)] {S : Type} [CommRing S] [Algebra c.F S] [Algebra ℚ S] {y : FrPt Xo c S}
    (C : ChartAt Xo c y) (k : ℕ) {n : ℕ} (f : Fin n → MvPowerSeries (Fin 1 × Fin C.d) S)
    (P : MvPolynomial (LtN Dw n) c.F) : S :=
  colSum c (fun b α => C.B.nabVal S C.h H.w0 k (f b) C.uvec (MvPolynomial.monomial α 1)) P

def sysVal (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (k : ℕ) {n : ℕ}
    (F : Fin n → SecAt Xo c y k) (P : MvPolynomial (LtN Dw n) c.F) : S :=
  colSum c (fun b α => nab y (k : ℤ) (F b) α) P

def IsHarmonic {n : ℕ} (P : MvPolynomial (LtN Dw n) c.F) : Prop :=
  ∀ (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) (i' : Fin (Dw.mult (ComplexEmbedding.conjugate τ))),
    ∑ b : Fin n, MvPolynomial.pderiv (⟨τ, i, b⟩ : LtN Dw n)
      (MvPolynomial.pderiv (⟨ComplexEmbedding.conjugate τ, i', b⟩ : LtN Dw n) P) = 0

def NabUnique : Prop :=
  ∀ [StarRing (𝓞 E)] (nab nab' : NabV Xo c), IsNab Xo c nab → IsNab Xo c nab' →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (k n : ℕ)
      (F : Fin n → SecAt Xo c y k) (P : MvPolynomial (LtN Dw n) c.F), IsHarmonic c P →
        sysVal Xo c nab y k F P = sysVal Xo c nab' y k F P

example {n : ℕ} (x : LtN Dw n) : IsHarmonic c (MvPolynomial.X x : MvPolynomial (LtN Dw n) c.F) := by
  classical
  intro τ i i'
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [MvPolynomial.pderiv_X, Pi.single_apply]
  split_ifs <;> simp

end GlobalTheory.IndefiniteRowSideFullHecke.HarmonicSystemChartValues
