import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefOfSemipositiveFibrewise
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nef_of_semipositive_fibrewise : Hypotheses2 → HypothesesH → ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (M : Adl C Y), M.SemiPos → M.NefFib → Y.nef M.D := by
  first | exact @GlobalTheory.CovHt.Link.nef_of_semiPos_nefFib | exact GlobalTheory.CovHt.Link.nef_of_semiPos_nefFib | (intros; apply GlobalTheory.CovHt.Link.nef_of_semiPos_nefFib <;> assumption)
