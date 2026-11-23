import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqExistsIffDsExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.IdemHalf

theorem infPart_eq_zero_of_isSplitIdem {D : D7} {e : AE D} (h : IsSplitIdem D e) :
    infPart D e = 0 ∧ infPart D (cA D e) = 0 := by
  obtain ⟨h1, h2, v, ε, ⟨α, rfl, -, -⟩, hε⟩ := h
  have hz : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
    show infPart D ((pairA D.host.F 0 α) ⊗ₜ[D.host.F] (1 : D.host.E)) = 0
    show (fstA D.host.F (pairA D.host.F 0 α)) ⊗ₜ[D.host.F] (1 : D.host.E) = 0
    rw [show fstA D.host.F (pairA D.host.F 0 α) = 0 from rfl, TensorProduct.zero_tmul]
  have hs : infPart D e + infPart D (cA D e) = 0 := by rw [← (infPart D).map_add, hε, hz]
  have hm : infPart D e * infPart D (cA D e) = 0 := by rw [← (infPart D).map_mul, h2, (infPart D).map_zero]
  have hi : infPart D e * infPart D e = infPart D e := by rw [← (infPart D).map_mul, h1]
  have hb : infPart D (cA D e) = - infPart D e := eq_neg_of_add_eq_zero_right hs
  rw [hb, mul_neg, hi] at hm
  have ha : infPart D e = 0 := neg_eq_zero.mp hm
  exact ⟨ha, by rw [hb, ha, neg_zero]⟩

theorem halfFin : ∀ {D : D7} (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ {m n : ℕ} (y : Mx D m n), (IsHalf e y ∨ IsHalf (cA D e) y) → y.map (infPart D) = 0 := by
  intro D P e he m n y hy
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  have h0 : infPart D (∑ PP ∈ P, es PP) = 0 := by
    rw [map_sum (infPart D)]
    exact Finset.sum_eq_zero fun PP hPP => (infPart_eq_zero_of_isSplitIdem (hes PP hPP).1).1
  have h1 : infPart D (cA D (∑ PP ∈ P, es PP)) = 0 := by
    rw [map_sum (cA D), map_sum (infPart D)]
    exact Finset.sum_eq_zero fun PP hPP => (infPart_eq_zero_of_isSplitIdem (hes PP hPP).1).2
  ext i j
  simp only [Matrix.map_apply, Matrix.zero_apply]
  rcases hy with hy | hy
  · rw [← hy i j, (infPart D).map_mul, h0, zero_mul]
  · rw [← hy i j, (infPart D).map_mul, h1, zero_mul]

end GlobalTheory.IdemHalf
