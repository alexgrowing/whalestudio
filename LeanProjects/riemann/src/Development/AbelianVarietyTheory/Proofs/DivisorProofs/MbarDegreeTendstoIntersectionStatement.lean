import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MbarDegreeTendstoIntersection
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mbar_degree_tendsto_intersection : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (L : CmList A) (x : ToroidalCompactificationData s) (P : Mean4O.PolOf x Φ) (B : ℝ) (u : AllWt.Weight S.Dw) (k : s.Comp), Tendsto (fun r : ℚ => (mbarOf P B (wtR L u) r k).deg) (𝓝[>] 0) (𝓝 ((Φ.C k).Y.inter fun _ => (Φ.C k).Lw u : ℝ)) ∧ ((∀ᶠ r : ℚ in 𝓝[>] 0, (Φ.C k).Y.nef (mbarOf P B (wtR L u) r k).D) → (Φ.C k).Y.nef ((Φ.C k).Lw u)) := by
  first | exact @GlobalTheory.CovHt.Link.tendsto_deg_mbarOf_and_nef | exact GlobalTheory.CovHt.Link.tendsto_deg_mbarOf_and_nef | (intros; apply GlobalTheory.CovHt.Link.tendsto_deg_mbarOf_and_nef <;> assumption)
