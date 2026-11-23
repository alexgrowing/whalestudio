import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormRankLeSections
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_form_rank_le_sections : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (Z : Comp s.Xo κ.c), Over Φ k Z → ∀ la : AllWt.Weight S.Dw, (∀ τ, Antitone (la τ)) → Cardinal.toENat (Module.rank κ.c.F (cuspOn (unf s) Z (wtOf S.Dw la 0))) ≤ Cardinal.toENat (Module.rank D.what₂.LL ((Φ.C k).Y.H0 ((Φ.C k).Lw la))) := by
  first | exact @GlobalTheory.CovHt.RankInj.rank_le | exact GlobalTheory.CovHt.RankInj.rank_le | (intros; apply GlobalTheory.CovHt.RankInj.rank_le <;> assumption)
