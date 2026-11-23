import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockDeltaBasePolynomial
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TauPsiApply
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_delta_base_polynomial : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (Dw : Datum H) (m n : ℕ) (hΨ : ∀ τ : D.host.E →+* ℂ, InPsi H τ ↔ ∃ ρ, τ = tauE D ρ) (hm : m = Dw.p + Dw.q) (w : Weight D n) (a : (D.host.E →+* ℂ) × ℕ → ℕ), WtIs Dw w a → ∀ (hn : Dw.p + Dw.q ≤ n), ∃ c : ℂ, MvPolynomial.rename (GlobalTheory.FockLetters.fockVarEquiv Dw hΨ hm) (w.delta m) = MvPolynomial.C c * GlobalTheory.Harm.basePoly ℂ hn (GlobalTheory.FockLetters.stepsX Dw a) (GlobalTheory.FockLetters.stepsY Dw a) := by
  first | exact @GlobalTheory.FockLetters.rename_delta_eq_smul_basePoly | exact GlobalTheory.FockLetters.rename_delta_eq_smul_basePoly | (intros; apply GlobalTheory.FockLetters.rename_delta_eq_smul_basePoly <;> assumption)
