import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiPeriodAllDataIsTameThetaFunctional
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobiPeriod_all_data_isTameThetaFunctional : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ σ : ℕ) (B : BesL D σ) (J : JacL D ρ) (χ χ' : (AE D)ˣ →* Circle) (om₀ : Om B.V₀ J.W₀), IsWeilDatumO ψ B.V₀ J.W₀ χ χ' om₀ → ∀ (φ : GA D B.A → ℂ) (G : GA D J.W → ℂ), RapidDec B.A φ → RapidDec J.W G → Tame ψ B.V₀ J.W₀ (J.perAll ψ B om₀ φ G) := by
  first | exact @GlobalTheory.PerAllTame.perAll_tame | exact GlobalTheory.PerAllTame.perAll_tame | (intros; apply GlobalTheory.PerAllTame.perAll_tame <;> assumption)
