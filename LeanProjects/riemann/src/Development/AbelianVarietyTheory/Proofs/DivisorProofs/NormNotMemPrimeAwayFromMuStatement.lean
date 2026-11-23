import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormNotMemPrimeAwayFromMu
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NuHTwisted
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField IsDedekindDomain
open GlobalTheory.FunObj.SqNum (nuH halfRank IsTor)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_not_mem_prime_away_from_mu : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (CF : ℝ) (d : FunIn p CF), p.Rows → Fitted (@Comparison₂) p CF d → ∀ w : HeightOneSpectrum (𝓞 D.what₂.LL), p.R.mu w ≠ p.P.A3.A.μ0 → ((Qn d.G (p.R.mu w) : ℕ) : 𝓞 D.what₂.LL) ∉ w.asIdeal := by
  first | exact @GlobalTheory.ThmAUpper.qn_not_mem | exact GlobalTheory.ThmAUpper.qn_not_mem | (intros; apply GlobalTheory.ThmAUpper.qn_not_mem <;> assumption)
