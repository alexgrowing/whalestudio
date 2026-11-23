import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatMapHeisenbergAndHomTransformation
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatMap_heisenberg_and_hom_transformation : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (s : Step ψ V V₀ W W₀ ρ σ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E) (y : Mx D V₀.rank σ), LinearIndependent D.host.E x₀.transpose → ∀ f, IsThetaFunO ψ V W f → (∀ N : Mx D ρ ρ, (∀ i j, j ≤ i → N i j = 0) → flatS dV dW s (rat x₀) y (heisO ψ V W (dV.extX W ((rat x₀ : Mx D W.rank ρ) ⬝ N)) f) = psiE ψ (upSum N) • flatS dV dW s (rat x₀) y f) ∧ ∀ ξ : Mx D σ V₀.rank, flatS dV dW s (rat x₀) y (heisO ψ V W (dV.ext0 W (dW.incX V₀ ξ)) f) = ψ (symplO V₀ W (dW.incAdj V₀ y) (dW.incX V₀ ξ)) • flatS dV dW s (rat x₀) y f := by
  first | exact @GlobalTheory.AscFlatLaws.flatS_laws | exact GlobalTheory.AscFlatLaws.flatS_laws | (intros; apply GlobalTheory.AscFlatLaws.flatS_laws <;> assumption)
