import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivLatticePartZeroIffMemNsmul
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltGraded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTorsionIsomorphism

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LowDat GlobalTheory.LowFilt
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_equiv_latticePart_zero_iff_mem_nsmul : ∀ (R : Type) [CommRing R] [IsDomain R] (D₀ : DegPre R), D₀.TauBimult →
    ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (n : ℕ), 0 < n → ∀ p : QkPt D₀ F n,
    (∃ q : QkPt D₀ F n, QkPt.Equiv D₀ F p q ∧ q.y = 0) ↔ ∃ e, p.y = n • e := by
  first | exact @GlobalTheory.LowFilt.exists_equiv_y_eq_zero_iff | exact GlobalTheory.LowFilt.exists_equiv_y_eq_zero_iff | (intros; apply GlobalTheory.LowFilt.exists_equiv_y_eq_zero_iff <;> assumption)
