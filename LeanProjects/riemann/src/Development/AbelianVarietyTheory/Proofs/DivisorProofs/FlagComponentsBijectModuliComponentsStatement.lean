import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagComponentsBijectModuliComponents
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_components_biject_moduli_components : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag), ∃ q : s.Comp ≃ Comp s.Xo κ.c, ∀ k, Over Φ k (q k) := by
  first | exact @GlobalTheory.CovHt.Link.exists_equiv_over | exact GlobalTheory.CovHt.Link.exists_equiv_over | (intros; apply GlobalTheory.CovHt.Link.exists_equiv_over <;> assumption)
