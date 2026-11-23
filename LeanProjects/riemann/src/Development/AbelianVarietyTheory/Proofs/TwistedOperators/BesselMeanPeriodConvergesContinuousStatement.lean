import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselMeanPeriodConvergesContinuous
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselMean_period_converges_continuous : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesL D ρ) (J : JacL D ρ) (s : StBF ψ B J), ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ) (Φ : WO B.V J.W → ℂ), RapidDec B.A φ → RapidDec J.W G → IsThetaFunO ψ B.V J.W Φ → (∀ h, AbsConv J.v0.μ J.v0.𝓕 J.vN.ν J.vN.𝓝 (fjAllFun ψ J.d B.o B.ζ s.om₀ B.vA.μ B.vA.𝓕 φ (rTrans h G) (flBF s (s.om (1, h) Φ)))) ∧ Continuous fun h => J.perAll ψ B s.om₀ φ (rTrans h G) (flBF s (s.om (1, h) Φ)) := by
  first | exact @GlobalTheory.BesMean.perAll_flBF_cont | exact GlobalTheory.BesMean.perAll_flBF_cont | (intros; apply GlobalTheory.BesMean.perAll_flBF_cont <;> assumption)
