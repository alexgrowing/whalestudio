import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT

namespace GlobalTheory.KeyFourth

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def Tied {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (s : LB.Sec (PPx x)) (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left))
    (Φ : FibKey Xo S x) : Prop :=
  SecTie Φ.m Φ.th s ∧ ∃ hg : Φ.T.g = g, ∀ i : Fin Φ.T.g,
    (Φ.v i).left ≫ Φ.m.φ = u (e (i.cast hg)).1 (e (i.cast hg)).2

def kch {S : Type} [CommRing S] (t : Ix Dw → Sˣ) : Sˣ := ∏ i, t i ^ keyEx Dw i

theorem kch_mul {S : Type} [CommRing S] (t t' : Ix Dw → Sˣ) : kch (t * t') = kch t * kch t' := by
  simp only [kch, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem kch_inv {S : Type} [CommRing S] (t : Ix Dw → Sˣ) : kch t⁻¹ = (kch t)⁻¹ := by
  simp only [kch, Pi.inv_apply, inv_zpow, Finset.prod_inv_distrib]

theorem kch_eq {S : Type} [CommRing S] (t : Ix Dw → Sˣ) :
    kch t = (∏ x : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)), t (some x)) * (t none ^ 2)⁻¹ := by
  rw [kch, Fintype.prod_option, mul_comm]
  simp only [keyEx, zpow_one, zpow_neg]
  rfl

def RootVal {σ : c.F →+* ℂ} {r : ℕ} (U : Formalism.L2.PjFree.Unf Xo c σ r) (y : FrPt Xo c (CAt σ)) (v : ℂ) : Prop :=
  ∃ (k : U.Comp) (x : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ), FrBor t (U.un k x) y ∧
    v = Formalism.L2.PjFree.toC ((kch t : (CAt σ)ˣ) : CAt σ)

end GlobalTheory.KeyFourth
