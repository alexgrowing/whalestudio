import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaKernelFockVectorEqOfFinitePointMove
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFlipDet
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKernel_fockVector_eq_of_finite_point_move : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (z : GA D V), z ∈ GfC V → ∀ (e e₂ : AE D) (M : ℕ) (O : Subring ℂ) (f f' : WO V W → ℂ) (a : ℂ), f ∈ trSp ψ V W ΛV ΛW f₀ e M O → f' ∈ trSp ψ V W ΛV ΛW f₀ e₂ M O → om (z, 1) f' = a • f → ∀ (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (Q : MvPolynomial (FVar D W.rank V.rank) ℂ) (s : GA D V) (g : GA D W), a * thetaKO om s g (stdF ψ θ V W sW BW f Q) = thetaKO om (s * z) g (stdF ψ θ V W sW BW f' Q) := by
  first | exact @GlobalTheory.LevelSeries.thetaKO_flip | exact GlobalTheory.LevelSeries.thetaKO_flip | (intros; apply GlobalTheory.LevelSeries.thetaKO_flip <;> assumption)
