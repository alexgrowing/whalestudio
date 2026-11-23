import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagTrivialNsmulCharP
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_trivial_nsmul_char_p : ∀ (p : ℕ), p.Prime → ∀ (Z : Scheme.{0}) [IsIntegral Z], (p : Γ(Z, ⊤)) = 0 → ∀ (N : ℕ) (g : Fin N → Pic Z), FlagOfTriv g → FlagOfTriv fun i => p • g i := by
  first | exact @GlobalTheory.TrivFlag.flagOfTriv_frob | exact GlobalTheory.TrivFlag.flagOfTriv_frob | (intros; apply GlobalTheory.TrivFlag.flagOfTriv_frob <;> assumption)
