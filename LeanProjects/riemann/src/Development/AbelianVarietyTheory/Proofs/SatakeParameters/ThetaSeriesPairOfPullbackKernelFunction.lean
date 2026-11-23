import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Reframe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TaylorDirLinear
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IteratedFDerivConstSmulOfNe
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TaylorSeriesMatrixPullbackEqLinearSubstitutionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DifferentiableOfUnitaryMatrixPullbackDifferentiaStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicSeriesAlgebraicMultipleViaPlaceExtensionStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PullbackThenFrameSubstitutionEqChangedFramesStatement
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.MainNotions Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert Formalism.UG Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances Formalism.L2.KerInert.SecondKernelSeries Formalism.L2.KerInert.QuadraticBaseChangeGL3 Formalism.L2.KerInert.SecondKernelDifference Formalism.L2.KerInert.SecondKernelHermitian GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwV.DelB TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.TwV.DelB

theorem linSub_smul' {σ R : Type} [Fintype σ] [CommRing R] (B : σ → σ → R) (a : R) (f : MvPowerSeries σ R) :
    linSub B (a • f) = a • linSub B f := by
  rw [MvPowerSeries.smul_eq_C_mul, MvPowerSeries.smul_eq_C_mul, GlobalTheory.TwU.LawAll.linSub_C_mul']

theorem map_linSub' {σ R S : Type} [Fintype σ] [CommRing R] [CommRing S] (h : R →+* S) (B : σ → σ → R)
    (f : MvPowerSeries σ R) :
    MvPowerSeries.map h (linSub B f) = linSub (fun x y => h (B x y)) (MvPowerSeries.map h f) := by
  unfold linSub
  exact GlobalTheory.PSerLin.map_subst_linear h B f

theorem frecG_pull : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (X : Sys p) (E : CEmb X.G) (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau) (fd : FData X D) (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : ℂ →+* ℂ_[p]), (∀ z : TaylorLogMetric.Qbar, ι z = lam z) → ∀ (ρ : ∀ v : X.Pl, D.host.E →+* X.G.P.Qq v), LamPos X E pos lam ρ → ∀ (e : ∀ j, X.Lt j → Matrix (Fin ((X.Pj j).m + 1)) (Fin ((X.Pj j).m + 1)) D.host.E) (c : ℂ_[p]) (j : ℕ) (La : X.Lt j) (La' : X.Lt (j + 1)), e j La * star (e j La) = 1 → e (j + 1) La' * star (e (j + 1) La') = 1 → ∀ {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ) (Ξ₀ : ∀ j, X.Lt j → X.Lt (j + 1) → Formalism.L2.Col.HomE D.host.E ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ) (muT : ℕ → (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)ˣ → ℂ), PairOK X fd B χ SS cl Ξ₀ muT ρ → j < X.mm → (X.Pj j).IsLatTup La.2 → (X.Pj (j + 1)).IsLatTup La'.2 → ∀ (s : ℂ) (Θ : TaylorLogMetric.VC D ((X.Pj j).m + 1) ((X.Pj (j + 1)).m + 1) → ℂ), s ≠ 0 → (∀ z, kerTh B χ SS cl (fd.kerN j La) (fd.kerN (j + 1) La') (xiM X fd Ξ₀ j La La') z = s * TaylorLogMetric.pull D B.tor (e j La) (e (j + 1) La') Θ z) → FrecG E pos fd B χ lam SS cl Ξ₀ muT c j La La' = linSub (fun x y => c * subBG E pos (reframe fd ρ e) j La La' x y) ((pPow X j La La' * ι (scal0 X fd χ muT j La La' * (Base.chiFac χ _ _ (fd.kerN j La) (fd.kerN (j + 1) La'))⁻¹ * s)) • MvPowerSeries.map ι (tay Θ)) := by
  intro D p _ X E pos fd lam ι hι ρ hρ e c j La La' he he' cc δ B χ SS cl Ξ₀ muT hok hj hL hL' s Θ hs hK
  obtain ⟨-, -, hdiff, hcoef, hsc, hcf, hcf0, hfr⟩ := hok j hj La La' hL hL'
  have hΘ : Differentiable ℂ Θ :=
    GlobalTheory.T.differentiable_of_unitary_matrixPullback_differentiable D cc δ (e j La) (e (j + 1) La') Θ _ s he he' hs hdiff hK
  have hsc' : scal0 X fd χ muT j La La' * (Base.chiFac χ _ _ (fd.kerN j La) (fd.kerN (j + 1) La'))⁻¹ ∈ TaylorLogMetric.Qbar :=
    TaylorLogMetric.Qbar.mul_mem hsc (TaylorLogMetric.Qbar.inv_mem hcf)
  have hser := GlobalTheory.T.padicSeries_algebraic_multiple_via_place_extension D p lam ι hι _ _ _ s hsc' hcoef hK
  have htay := GlobalTheory.T.taylorSeries_matrixPullback_eq_linear_substitution D cc δ (e j La) (e (j + 1) La') Θ hΘ
  have hsub := GlobalTheory.T.pullback_then_frame_substitution_eq_changed_frames D p X E pos fd lam ι hι ρ hρ e c j La La' he he' (fun v => ⟨(hfr v).1, (hfr v).2.1⟩)
  rw [frecG_eq, hser]
  change linSub _ (_ • _ • MvPowerSeries.map ι (tay (TaylorLogMetric.pull D (TaylorLogMetric.tor0 D cc δ) (e j La) (e (j + 1) La') Θ))) = _
  rw [htay, map_linSub', ← linSub_smul', ← linSub_smul', GlobalTheory.TwU.LawAll.linSub_linSub', smul_smul]
  congr 1
  funext x y
  exact hsub x y

end GlobalTheory.TwV.DelB
