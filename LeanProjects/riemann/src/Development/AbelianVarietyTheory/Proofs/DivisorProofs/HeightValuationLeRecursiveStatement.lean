import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightValuationLeRecursive
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_valuation_le_recursive : GlobalTheory.CovHt.HTDiag.DiagBound → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsGalois ℚ E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) (pl : HeightOneSpectrum (𝓞 c.F)), p.Prime → (p : 𝓞 c.F) ∈ pl.asIdeal → ∀ w ∈ (htVals Xo c).1 pl, ∃ v ∈ (recVals Xo c).1 pl, ∀ (u : AllWt.Weight Dw), ∀ f ∈ secZ Xo c (exOf Dw u 0), v f ≤ w f + (((vLa pl (p : c.F) : ℝ) * htEx E p * l1 u : ℝ) : EReal) := by
  first | exact @GlobalTheory.CovHt.HTLink.recVal_le | exact GlobalTheory.CovHt.HTLink.recVal_le | (intros; apply GlobalTheory.CovHt.HTLink.recVal_le <;> assumption)
