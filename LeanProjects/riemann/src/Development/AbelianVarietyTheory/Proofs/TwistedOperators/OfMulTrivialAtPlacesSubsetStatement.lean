import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OfMulTrivialAtPlacesSubset
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.of_mul_trivialAtPlaces_subset : ∀ {D : D7} {V₀ W W₀ : HSp D} {ρ σ : ℕ} (dW : HypDec W W₀ σ) (p : Pieces V₀ W W₀ ρ σ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (ψ : AddChar (AF D.host.F) ℂ) (P Q : GlobalTheory.FinPl.Pl D → Prop) (g₁ g₂ : GA D W), (∀ v, Q v → P v) → g₁ ∈ grpAt W Q → g₂ ∈ grpOff W Q → g₁ * g₂ = g₂ * g₁ → Cond dW p x y ψ P (g₁ * g₂) → Cond dW p x y ψ Q g₁ := by
  first | exact @GlobalTheory.AscFin.Cond.of_mul_grpOff | exact GlobalTheory.AscFin.Cond.of_mul_grpOff | (intros; apply GlobalTheory.AscFin.Cond.of_mul_grpOff <;> assumption)
