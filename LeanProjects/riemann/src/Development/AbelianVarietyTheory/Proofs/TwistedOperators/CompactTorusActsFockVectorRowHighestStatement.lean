import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactTorusActsFockVectorRowHighest
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactTorus_acts_fockVector_rowHighest : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ B, C.IsB B → ∀ f, C.IsTh f → C.IsFock B f → ∀ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) (Q : MvPolynomial (FVar D T.rank S.rank) ℂ), C.toH Q ∈ Harm.rowHighest ℂ c c' → ∀ (ρ : D.what₂.Tau) (t : Fin T.rank → ℝ) (m : D.what₂.Tau → ℤ), RealScal C om B (torAt C.θ T B ρ t) (detPow C.θ T m (torAt C.θ T B ρ t)) → torAt C.θ T B ρ t ∈ GinfC T ∧ om (1, torAt C.θ T B ρ t) (C.fvec B f Q) = cexp (((∑ a, ((m ρ - ThFr.wtOf C.X C.hr c c' S.rank (C.m.e ρ) a : ℤ) : ℝ) * t a : ℝ) : ℂ) * I) • C.fvec B f Q := by
  first | exact @GlobalTheory.AdSpan.TorWt.torAt_fvec | exact GlobalTheory.AdSpan.TorWt.torAt_fvec | (intros; apply GlobalTheory.AdSpan.TorWt.torAt_fvec <;> assumption)
