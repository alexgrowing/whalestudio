import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepZeroApproximationTwistPrimes
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsChartsReadingStepZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepZero_approximation_twistPrimes : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (β : Ch 0), A.kb 0 β = TC.kStd X u (B.R.N 0) → ∀ (c : {c // A.chOf 0 c = β}) (x : TC.GA B (B.R.N 0)), x ∈ Formalism.L2.Col.UAd B.sp.cm (B.R.N 0) → ∃ h : TC.GA B (B.R.N 0), h ∈ (A.K 0 (Nat.zero_le _) β).lev.U ∧ h ∈ Formalism.L2.Col.levU (F := B.host.F) B.sp.cm (B.R.N 0) ((B.primes X).vT u) (B.primes X).vGs (Formalism.L2.Col.colLev I.Ch 0).grp ∧ ∃ q : Formalism.L2.Col.ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u 0, TC.PtOf ((show TC.GA B (B.R.N 0) from ((A.K 0 (Nat.zero_le _) β).y c).1) * (x * h) * TC.kStd X u (B.R.N 0)) q := by
  first | exact @GlobalTheory.ApproxZero.approx_zero | exact GlobalTheory.ApproxZero.approx_zero | (intros; apply GlobalTheory.ApproxZero.approx_zero <;> assumption)
