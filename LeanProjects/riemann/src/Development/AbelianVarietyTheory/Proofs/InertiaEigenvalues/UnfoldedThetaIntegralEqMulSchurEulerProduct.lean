import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralRankinSelbergThetaEqWhittakerUnfoldingStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralThetaSelfCuspRapidSpanNeTopStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergThetaIntegralSmoothSpanEqToRealLintStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsFundamentalDomainRationalUpperUnitrianguStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedWhittakerIntegralEqEulerProductSchurSumsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors

namespace GlobalTheory.RSEulerId

theorem thetaZ_eq_mul_eulD : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CG E a), 1 ≤ a → π.IsUnitary →
    ∀ T : Finset (HeightOneSpectrum (𝓞 E)), UnrOutside T π →
    ∃ (α : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} → Fin a → ℂˣ) (ℓ : Fin a) (Φ : (Fin a → Cinf E) → ℂ)
      (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (π₀ : CuspSub E a) (ω : HChar E) (φ : Sm E a),
      (∀ w, Finset.univ.val.map (α w) = sat π w) ∧ CG.mk π₀ = π ∧ ω.IsUnitary ∧ π₀.HasCentChar ω ∧
      (φ ∈ π₀.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π₀) ∧ φ ≠ 0 ∧
      ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ ∧
      (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) ∧ Φ ≠ 0 ∧
      ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ →
        ∃ H : ℝ → ℝ, ContinuousWithinAt H (Set.Ioi 1) 1 ∧ 0 < H 1 ∧ ∀ x : ℝ, 1 < x → 0 < H x ∧
          GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
                       (fun w i => ((α w i : ℂˣ) : ℂ)) x ≠ ⊤ ∧
          GlobalTheory.RSPole.thetaZ μ 𝓕 ℓ φ.1 φ.1 Φ J η x =
            ((H x * (GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
              (fun w i => ((α w i : ℂˣ) : ℂ)) x).toReal : ℝ) : ℂ) := by
  intro E _ _ _ a π ha hu T hT
  obtain ⟨α, ℓ, Φ, J, η, π₀, ω, φ, hℓ, hα, hπ₀, hω, hc, hφ, hφ0, hΦs, hΦc, hΦr, hΦp, hΦ0, hcore⟩ :=
    GlobalTheory.T.unfoldedWhittakerIntegral_eq_eulerProduct_schurSums E a π ha hu T hT
  have hF : φ.1 ∈ GlobalTheory.JSW.mspanR π₀ := hφ.elim (fun h => Submodule.mem_sInf.2 fun _ hS => hS.1 φ h) id
  have hπu : π₀.IsUnitary := ⟨ω, hω, CuspSub.hasCentral_iff.2 hc⟩
  have hFc : Continuous φ.1 := by
    obtain ⟨ψ, hψ, hw⟩ := GlobalTheory.JSW.mspanR_words GlobalTheory.CuspOrth.cuspFormsBounded hπu φ.1 hF
    have h0 := (hw []).2
    rw [GlobalTheory.JSW.word_nil, hψ] at h0
    exact h0.cont
  refine ⟨α, ℓ, Φ, J, η, π₀, ω, φ, hα, hπ₀, hω, hc, hφ, hφ0, hΦs, hΦc, hΦr, hΦp, hΦ0, fun μ _ 𝓕 h𝓕 => ?_⟩
  obtain ⟨𝓕₀, h𝓕₀⟩ := GlobalTheory.T.exists_isFundamentalDomain_rationalUpperUnitriangular E a μ
  obtain ⟨H, hHc, hH1, hH⟩ := hcore μ 𝓕₀ h𝓕₀
  refine ⟨H, hHc, hH1, fun x hx => ?_⟩
  obtain ⟨hHx, heq⟩ := hH x hx
  have hU := GlobalTheory.T.lintegral_rankinSelbergTheta_eq_whittakerUnfolding E a ℓ hℓ π₀ hπu φ.1 hF Φ hΦs.continuous hΦc hΦr J η μ 𝓕 𝓕₀ h𝓕 h𝓕₀ x
  have hfin := GlobalTheory.T.lintegral_theta_self_cusp_rapid_span_ne_top E a ℓ π₀ ω hω hc φ.1 hF Φ hΦs hΦc hΦr hΦp J η μ 𝓕 h𝓕 x hx
  have hZ := GlobalTheory.T.rankinSelbergThetaIntegral_smoothSpan_eq_toReal_lintegral E a ℓ π₀ φ.1 hF hFc Φ hΦs.continuous hΦr hΦp J η μ 𝓕 h𝓕 x hfin
  rw [hU, heq] at hfin hZ
  refine ⟨hHx, fun h => hfin (by rw [h, ENNReal.mul_top (ENNReal.ofReal_pos.2 hHx).ne']), ?_⟩
  rw [hZ, ENNReal.toReal_mul, ENNReal.toReal_ofReal hHx.le]

end GlobalTheory.RSEulerId
