import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ZintZero
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBumpShintaniStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedThetaIntegralEqMulSchurEulerProductStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultisetProdMapProductEqProdProd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdTsumEqTsumIndicatorEnnreal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumRankinSelbergSchurTermFinsuppEulerProductStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExpIntegralEntireRealPosStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PolarisedThetaIntegralUnfoldWhittakerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedPolarisedIntegralBumpedFormsStatement

import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedOutsideOfConductor

noncomputable section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.RSJ GlobalTheory.ZEul Filter Topology Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate

namespace GlobalTheory.ZEul.Smooth

theorem zint_eq_mul_partialL_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (σ σ' : CG E a), 1 ≤ a → σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), (∀ w ∈ T, ∀ w' : HeightOneSpectrum (𝓞 E), Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal = Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal → w' ∈ T) → (∀ w ∉ T, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w) → UnrOutside T σ → UnrOutside T σ' → ∃ (N : ℕ) (Φ : (Fin a → Cinf E) → ℂ) (π π' : CuspSub E a) (φ φ' : GA E a → ℂ), CG.mk π = σ ∧ CG.mk π' = σ' ∧ φ ∈ GlobalTheory.JSW.mspanR π ∧ φ' ∈ GlobalTheory.JSW.mspanR π' ∧ φ ≠ 0 ∧ φ' ≠ 0 ∧ 0 < N ∧ ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ (∀ ℓ : Fin a, (ℓ : ℕ) + 1 = a → tsupport Φ ⊆ {u | ∀ w, u ℓ w ≠ 0}) ∧ ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ (∀ x : ℝ, 0 < (H x).re ∧ (H x).im = 0) ∧ ∀ x : ℝ, 1 < x → GlobalTheory.RSJ.Zint μ 𝓕 φ φ' Φ N x = H x * ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) ∧ GlobalTheory.RSJ.Zint μ 𝓕 φ φ Φ N x = H x * ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) ∧ GlobalTheory.RSJ.Zint μ 𝓕 φ' φ' Φ N x = H x * ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ' w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) := by
  intro E _ _ _ a σ σ' ha hσ hσ' T hTs hψ hT hT'
  obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
  obtain ⟨α, _ℓ, _Φ, _J, _η, π, ω, _φ, hα, hπ, hω, hωc, _h1, _h2, _h3, _h4, _h5, _h6, _h7, hZ⟩ := GlobalTheory.T.unfolded_theta_integral_eq_mul_schur_euler_product E (m + 1) σ ha hσ T hT
  obtain ⟨α', _ℓ', _Φ', _J', _η', π', ω', _φ', hα', hπ', hω', hωc', _h1', _h2', _h3', _h4', _h5', _h6', _h7', hZ'⟩ :=
    GlobalTheory.T.unfolded_theta_integral_eq_mul_schur_euler_product E (m + 1) σ' ha hσ' T hT'
  subst hπ hπ'
  obtain ⟨μ₀, hμ₀, 𝓕₁, h𝓕₁⟩ : ∃ (μ : Measure (GA E (m + 1))) (_ : μ.IsHaarMeasure) (𝓕 : Set (GA E (m + 1))),
      IsFundamentalDomain (ratGL E (m + 1)).range 𝓕 μ := by
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E (m + 1)
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E (m + 1)
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E (m + 1)
    haveI : DiscreteTopology (ratGL E (m + 1)).range := GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E (m + 1)
    obtain ⟨𝓕, -, -, h𝓕⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (ratGL E (m + 1)).range
    exact ⟨Measure.haar, inferInstance, 𝓕, h𝓕 _⟩
  have hfin : ∀ x : ℝ, 1 < x → GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
      (fun w i => ((α w i : ℂˣ) : ℂ)) x ≠ ⊤ := fun x hx => by
    obtain ⟨H, -, -, h⟩ := hZ μ₀ 𝓕₁ h𝓕₁
    exact (h x hx).2.1
  have hfin' : ∀ x : ℝ, 1 < x → GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
      (fun w i => ((α' w i : ℂˣ) : ℂ)) x ≠ ⊤ := fun x hx => by
    obtain ⟨H, -, -, h⟩ := hZ' μ₀ 𝓕₁ h𝓕₁
    exact (h x hx).2.1
  classical
  let αe : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ := fun w => if h : w ∉ T then α ⟨w, h⟩ else fun _ => 1
  let αe' : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ := fun w => if h : w ∉ T then α' ⟨w, h⟩ else fun _ => 1
  have hαe : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, αe w.1 = α w := fun w => dif_pos w.2
  have hαe' : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, αe' w.1 = α' w := fun w => dif_pos w.2
  have hsatσ : ∀ (ρ : CuspSub E (m + 1)) (w : HeightOneSpectrum (𝓞 E)), (∃ B, (CG.mk ρ).HasSat w B) →
      HasSatGL w (ρ.locRep w) (sat (CG.mk ρ) w) := fun ρ w h => by
    rw [← CG.hasSat_mk, sat, dif_pos h]
    exact h.choose_spec
  have hs : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, Finset.univ.val.map (αe w.1) = sat (CG.mk π) w.1 := fun w => by
    rw [hαe w]; exact hα w
  have hs' : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, Finset.univ.val.map (αe' w.1) = sat (CG.mk π') w.1 := fun w => by
    rw [hαe' w]; exact hα' w
  have hsat : ∀ w ∉ T, HasSatGL w (π.locRep w) (Finset.univ.val.map (αe w)) := fun w hw => by
    rw [hs ⟨w, hw⟩]; exact hsatσ π w (hT w hw)
  have hsat' : ∀ w ∉ T, HasSatGL w (π'.locRep w) (Finset.univ.val.map (αe' w)) := fun w hw => by
    rw [hs' ⟨w, hw⟩]; exact hsatσ π' w (hT' w hw)
  obtain ⟨b, hb1, hbN, hbC, hbF⟩ := GlobalTheory.T.exists_bump_shintani_alt E m T hψ
  obtain ⟨φ, hφR, hU, hK, hW⟩ := hbF π αe hsat
  obtain ⟨φ', hφR', hU', hK', hW'⟩ := hbF π' αe' hsat'
  obtain ⟨hφ0, hφ0', N, Φ, hN, hΦc, hΦs, hΦr, hΦp, hC2⟩ := GlobalTheory.T.unfolded_polarised_integral_bumped_forms E m T hTs hψ b hb1 hbN hbC π π' ω ω' hω hω' hωc hωc' αe αe'
    hsat hsat' φ φ' hφR hφR' hU hK hU' hK' hW hW'
  refine ⟨N, Φ, π, π', φ, φ', rfl, rfl, hφR, hφR', hφ0, hφ0', hN, hΦc, hΦs, ?_, ?_⟩
  · intro ℓ hℓ
    have hl : ℓ = Fin.last m := Fin.ext (by simp only [Fin.val_last]; omega)
    subst hl
    exact hΦr
  intro μ hμ 𝓕 h𝓕
  obtain ⟨𝓕₀, h𝓕₀⟩ := GlobalTheory.ZEul.exists_fundamentalDomain_NE E (m + 1) μ
  obtain ⟨c, hc, hC1⟩ := GlobalTheory.T.polarisedThetaIntegral_unfold_whittaker E m μ
  obtain ⟨f, t, hfm, htm, hf0, hfi, hfpos, hR, hid⟩ := hC2 μ 𝓕₀ h𝓕₀
  obtain ⟨hdiff, hreal⟩ := GlobalTheory.T.exp_integral_differentiable_real_re_pos (μ.restrict 𝓕₀) f t hfm htm hf0 hfi hR
  refine ⟨fun s => (c : ℂ) * ∫ g in 𝓕₀, (f g : ℂ) * Complex.exp (s * t g) ∂μ, (differentiable_const _).mul hdiff, ?_, ?_⟩
  · intro x
    obtain ⟨him, hre⟩ := hreal x
    have hre' := hre hfpos
    refine ⟨?_, ?_⟩
    · simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact mul_pos hc hre'
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, him, mul_zero]
  · intro x hx
    have hq : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, 2 ≤ Ideal.absNorm w.1.asIdeal :=
      fun w => HeightOneSpectrum.one_lt_absNorm w.1
    have e1 : (fun (w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}) (i : Fin (m + 1)) => ((αe w.1 i : ℂˣ) : ℂ)) =
        fun w i => ((α w i : ℂˣ) : ℂ) := by funext w i; rw [hαe w]
    have e1' : (fun (w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}) (i : Fin (m + 1)) => ((αe' w.1 i : ℂˣ) : ℂ)) =
        fun w i => ((α' w i : ℂˣ) : ℂ) := by funext w i; rw [hαe' w]
    have hf1 : GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
        (fun w i => ((αe w.1 i : ℂˣ) : ℂ)) x ≠ ⊤ := by rw [e1]; exact hfin x hx
    have hf1' : GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
        (fun w i => ((αe' w.1 i : ℂˣ) : ℂ)) x ≠ ⊤ := by rw [e1']; exact hfin' x hx
    obtain ⟨hd, hd', e12, e11, e22⟩ := hid x hx hf1 hf1'
    have z12 := (hC1 π π' ω ω' hω hω' hωc hωc' φ φ' hφR hφR' N Φ hN hΦc hΦs hΦr hΦp 𝓕 𝓕₀ h𝓕 h𝓕₀ x hx hd hd').2
    have z11 := (hC1 π π ω ω hω hω hωc hωc φ φ hφR hφR N Φ hN hΦc hΦs hΦr hΦp 𝓕 𝓕₀ h𝓕 h𝓕₀ x hx hd hd).2
    have z22 := (hC1 π' π' ω' ω' hω' hω' hωc' hωc' φ' φ' hφR' hφR' N Φ hN hΦc hΦs hΦr hΦp 𝓕 𝓕₀ h𝓕 h𝓕₀ x hx hd' hd').2
    have A12 := (GlobalTheory.T.hasSum_rankinSelbergSchurTerm_finsupp_eulerProduct (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
      (fun w => αe w.1) (fun w => αe' w.1) x hx hq hf1 hf1').tsum_eq
    have A11 := (GlobalTheory.T.hasSum_rankinSelbergSchurTerm_finsupp_eulerProduct (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
      (fun w => αe w.1) (fun w => αe w.1) x hx hq hf1 hf1).tsum_eq
    have A22 := (GlobalTheory.T.hasSum_rankinSelbergSchurTerm_finsupp_eulerProduct (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
      (fun w => αe' w.1) (fun w => αe' w.1) x hx hq hf1' hf1').tsum_eq
    simp only [hs, hs'] at A12 A11 A22
    refine ⟨?_, ?_, ?_⟩
    · rw [z12, e12, A12]; ring
    · rw [z11, e11, A11]; ring
    · rw [z22, e22, A22]; ring

end GlobalTheory.ZEul.Smooth
