import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticVolumeLeCount
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeVolSlopeOfTendsto
open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovHt.Link GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_volume_le_count : GlobalTheory.Published.VolGe → GlobalTheory.Published.ArCalc → GlobalTheory.Published.ArDegree → ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (M : Adl C Y), M.SemiPos → M.NefFib → ∀ (t : ℝ) (cf : HeightOneSpectrum (𝓞 F) → ℝ), (Function.support cf).Finite → ∀ a : ℕ, 0 < a → ENNReal.ofReal (M.arTop / ((Y.dim : ℝ) + 1) + M.deg * (t + (∑ᶠ v, cf v) / (Module.finrank ℚ F : ℝ))) ≤ countVol Y.dim (Module.finrank ℚ F) a fun τ => ((M.twist (fun _ => t) cf).small τ).encard := by
  first | exact @GlobalTheory.CovHt.HodgeCount.twist_le_countVol | exact GlobalTheory.CovHt.HodgeCount.twist_le_countVol | (intros; apply GlobalTheory.CovHt.HodgeCount.twist_le_countVol <;> assumption)
