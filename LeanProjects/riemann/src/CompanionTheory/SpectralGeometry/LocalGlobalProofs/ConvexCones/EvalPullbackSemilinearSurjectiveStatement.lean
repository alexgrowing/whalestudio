import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.EvalPullbackSemilinearSurjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalPullSemilinearOfIsTwInv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eval_pullback_semilinear_surjective : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (φ : InvFun O), IsTwG w0 φ →
  ∀ {X Y : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] [AddCommGroup Y] [Module O Y] [Module.Finite O Y]
    (τ : O ≃+* O), τ w0 = w0 → ∀ (f : X →+ Y), Function.Surjective f → (∀ (a : O) (x : X), f (a • x) = τ a • f x) →
    ∀ B : Y → Y → ℝ, φ.eval X (fun x y => B (f x) (f y)) = φ.eval Y B := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fan.SemilinearPullbackEval.eval_pull_semilinear_of_isTwG | exact GlobalTheory.CompanionTheory.Ar.Fan.SemilinearPullbackEval.eval_pull_semilinear_of_isTwG | (intros; apply GlobalTheory.CompanionTheory.Ar.Fan.SemilinearPullbackEval.eval_pull_semilinear_of_isTwG <;> assumption)
