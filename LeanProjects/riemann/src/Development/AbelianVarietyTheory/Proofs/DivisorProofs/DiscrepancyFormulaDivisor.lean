import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOrdEqMultOfIsCartierDivisorOfRationalFormStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.Discrepancy

theorem discrep_isAt_eq_neg_mult : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (η : RatForms q n), η ≠ 0 → ∀ (K G : CartierDiv Y) (m : ℕ), 0 < m → IsDivOfForm K η → ∀ (E : DivOver q) (w : Y) (g : Y.functionFieldˣ), E.IsAt w → G.IsEqn w g → discrep E η m g = -((G - m • K).mult w : ℚ) / m := by
  intro k _ _ Y _ _ q n _ η hη K G m hm hK E w g hE hg
  obtain ⟨c, hc⟩ := K.exists_isEqn w
  have h1 := (hg.sub (hc.nsmul m)).mult_eq
  rw [← hE.ord_eq, div_eq_mul_inv, E.ord_mul, E.ord_inv, E.ord_pow] at h1
  have h2 := GlobalTheory.T.formOrd_eq_mult_of_isCartierDivisorOfRationalForm k Y q n η hη K hK E w hE
  rw [hc.mult_eq, ← hE.ord_eq] at h2
  have : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [discrep, h1, h2]
  push_cast
  field_simp
  ring

end GlobalTheory.Discrepancy
