import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadNatZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ZintZero
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsIntegralEntireGood
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedThetaIntegralEqMulSchurEulerProductStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIsFundamentalDomainAndQuotMeasureEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExpIntegralEntireRealPos
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMatchedWhittakerVectorsShintaniRelationsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergGLnGLmUnfoldingToMirabolicStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedRankinSelbergCellIntegralMatchedVectorsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerProductRankinSelbergGLnGLmDirichletSeriesStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff

namespace GlobalTheory.RSnmUnf

theorem rs_nm_partialL_eq_div : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n m : ℕ) (σ : CG E n) (σ' : CG E m), 1 ≤ m → m < n → σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), (∀ w ∉ T, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w) → UnrOutside T σ → UnrOutside T σ' → ∃ F H : ℂ → ℂ, Differentiable ℂ F ∧ Differentiable ℂ H ∧ (∀ x : ℝ, 0 < (H x).re ∧ (H x).im = 0) ∧ ∀ x : ℝ, 1 < x → HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) (F x / H x) := by
  intro E _ _ _ n m σ σ' hm hmn hσ hσ' T hψ hT hT'
  obtain ⟨m₀, rfl⟩ : ∃ m₀, m = m₀ + 1 := ⟨m - 1, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r, n = m₀ + r + 1 + 1 := ⟨n - m₀ - 2, by omega⟩
  obtain ⟨α, _ℓ, _Φ, _J, _η, π, _ω, _φ, hα, hπ, hω, hωc, _h1, _h2, _h3, _h4, _h5, _h6, _h7, hZ⟩ :=
    GlobalTheory.T.unfolded_theta_integral_eq_mul_schur_euler_product E (m₀ + r + 1 + 1) σ (by omega) hσ T hT
  obtain ⟨β, _ℓ', _Φ', _J', _η', π', _ω', _φ', hβ, hπ', hω', hωc', _h1', _h2', _h3', _h4', _h5', _h6', _h7', hZ'⟩ :=
    GlobalTheory.T.unfolded_theta_integral_eq_mul_schur_euler_product E (m₀ + 1) σ' (by omega) hσ' T hT'
  subst hπ hπ'
  have hu : π.IsUnitary := (CG.isUnitary_mk π).1 hσ
  have hu' : π'.IsUnitary := (CG.isUnitary_mk π').1 hσ'
  have hfd : ∀ a : ℕ, ∃ (μ : Measure (GA E a)) (_ : μ.IsHaarMeasure) (𝓕 : Set (GA E a)) (𝓕₀ : Set (GA E a)),
      IsFundamentalDomain (ratGL E a).range 𝓕 μ ∧ IsFundamentalDomain (GlobalTheory.CellDec.NE E a) 𝓕₀ μ := by
    intro a
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E a
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E a
    haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E a
    haveI : DiscreteTopology (ratGL E a).range := GroundTheory.Automorphic.AdelicGLn.discreteTopology_rationalGL E a
    have hsub : (GlobalTheory.CellDec.NE E a : Set (GA E a)) ⊆ ((ratGL E a).range : Set (GA E a)) := by
      rintro _ ⟨u, -, rfl⟩
      exact ⟨u, rfl⟩
    haveI : DiscreteTopology (GlobalTheory.CellDec.NE E a) :=
      DiscreteTopology.of_subset (inferInstance : DiscreteTopology ((ratGL E a).range : Set (GA E a))) hsub
    obtain ⟨𝓕, -, -, h𝓕⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (ratGL E a).range
    obtain ⟨𝓕₀, -, -, h𝓕₀⟩ := GlobalTheory.exists_isFundamentalDomain_subgroup (GlobalTheory.CellDec.NE E a)
    exact ⟨Measure.haar, inferInstance, 𝓕, 𝓕₀, h𝓕 _, h𝓕₀ _⟩
  obtain ⟨μ₁, hμ₁, 𝓕₁, -, h𝓕₁, -⟩ := hfd (m₀ + r + 1 + 1)
  obtain ⟨μ, hμ, 𝓕, 𝓕₀, h𝓕, h𝓕₀⟩ := hfd (m₀ + 1)
  have hfin : ∀ x : ℝ, 1 < x → GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
      (fun w i => ((α w i : ℂˣ) : ℂ)) x ≠ ⊤ := fun x hx => by
    obtain ⟨H, -, -, h⟩ := hZ μ₁ 𝓕₁ h𝓕₁
    exact (h x hx).2.1
  have hfin' : ∀ x : ℝ, 1 < x → GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
      (fun w i => ((β w i : ℂˣ) : ℂ)) x ≠ ⊤ := fun x hx => by
    obtain ⟨H, -, -, h⟩ := hZ' μ 𝓕 h𝓕
    exact (h x hx).2.1
  classical
  let αe : HeightOneSpectrum (𝓞 E) → Fin (m₀ + r + 1 + 1) → ℂˣ := fun w => if h : w ∉ T then α ⟨w, h⟩ else fun _ => 1
  let βe : HeightOneSpectrum (𝓞 E) → Fin (m₀ + 1) → ℂˣ := fun w => if h : w ∉ T then β ⟨w, h⟩ else fun _ => 1
  have hαe : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, αe w.1 = α w := fun w => dif_pos w.2
  have hβe : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, βe w.1 = β w := fun w => dif_pos w.2
  have hsatσ : ∀ {a : ℕ} (ρ : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)), (∃ B, (CG.mk ρ).HasSat w B) →
      HasSatGL w (ρ.locRep w) (sat (CG.mk ρ) w) := fun ρ w h => by
    rw [← CG.hasSat_mk, sat, dif_pos h]
    exact h.choose_spec
  have hsat : ∀ w ∉ T, HasSatGL w (π.locRep w) (Finset.univ.val.map (αe w)) := fun w hw => by
    rw [hαe ⟨w, hw⟩, hα ⟨w, hw⟩]; exact hsatσ π w (hT w hw)
  have hsat' : ∀ w ∉ T, HasSatGL w (π'.locRep w) (Finset.univ.val.map (βe w)) := fun w hw => by
    rw [hβe ⟨w, hw⟩, hβ ⟨w, hw⟩]; exact hsatσ π' w (hT' w hw)
  obtain ⟨φ, φ', κ, hφ, hφ', v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13⟩ :=
    GlobalTheory.T.exists_matchedWhittakerVectors_shintaniRelations E m₀ r T hψ π π' hu hu' αe βe hsat hsat'
  obtain ⟨F, hF, hC⟩ := GlobalTheory.T.unfolded_rankinSelberg_cellIntegral_matchedVectors E m₀ r T hψ π π' hu hu' αe βe φ φ' κ hφ hφ' v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13
  obtain ⟨c, hc, hU⟩ := GlobalTheory.T.rankinSelbergGLnGLm_unfolding_to_mirabolic E m₀ r μ
  obtain ⟨f, t, hfm, htm, hf0, hfi, hfpos, hR, hid⟩ := hC μ 𝓕₀ h𝓕₀
  obtain ⟨hdiff, hreal⟩ := GlobalTheory.exp_integral_entire_real_pos (μ.restrict 𝓕₀) f t hfm htm hf0 hfi hR
  have hlt : m₀ + 1 < m₀ + r + 1 + 1 := by omega
  have hent := GlobalTheory.RSnmGood.rsIntegral_entire_good (by omega) hlt
    (GlobalTheory.RSnmGood.mspanR_le_goodFns (by omega) hu hφ) (GlobalTheory.RSnmGood.mspanR_le_goodFns (by omega) hu' hφ') hF μ h𝓕
  refine ⟨fun s => ∫ h in 𝓕, GlobalTheory.RSnm.rsIntegrand (m₀ + 1) hlt.le F φ φ' s h ∂μ,
    fun s => (c : ℂ) * ∫ g in 𝓕₀, (f g : ℂ) * Complex.exp (s * t g) ∂μ, fun s => (hent.2 s).differentiableAt,
    (differentiable_const _).mul hdiff, ?_, ?_⟩
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
    have e1 : (fun (w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}) (i : Fin (m₀ + r + 1 + 1)) => ((αe w.1 i : ℂˣ) : ℂ)) =
        fun w i => ((α w i : ℂˣ) : ℂ) := by funext w i; rw [hαe w]
    have e1' : (fun (w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}) (i : Fin (m₀ + 1)) => ((βe w.1 i : ℂˣ) : ℂ)) =
        fun w i => ((β w i : ℂˣ) : ℂ) := by funext w i; rw [hβe w]
    have hf1 := hfin x hx
    have hf1' := hfin' x hx
    rw [← e1] at hf1
    rw [← e1'] at hf1'
    obtain ⟨dd1, dd2, eq⟩ := hid x hx hf1 hf1'
    obtain ⟨-, eU⟩ := hU π π' hu hu' φ φ' hφ hφ' F hF 𝓕 𝓕₀ h𝓕 h𝓕₀ x dd1 dd2
    rw [e1] at hf1
    rw [e1'] at hf1'
    obtain ⟨P, hP, hS⟩ := GlobalTheory.T.eulerProduct_rankinSelbergGLnGLm_dirichletSeries (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => Ideal.absNorm w.1.asIdeal)
      (by omega : m₀ + 1 ≤ m₀ + r + 1 + 1) α β x hx hq hf1 hf1'
    have hsum : (∑' l : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} →₀ (Fin (m₀ + 1) → ℤ),
        l.prod fun w v => GlobalTheory.RSnmUnf.rsTermNM (Ideal.absNorm w.1.asIdeal) (fun i => (αe w.1 i : ℂ))
          (fun i => (βe w.1 i : ℂ)) x v) = P := by
      simp only [hαe, hβe]
      exact hS.tsum_eq
    have hJ : (∫ g in 𝓕₀, (f g : ℂ) * Complex.exp ((x : ℂ) * t g) ∂μ) ≠ 0 := by
      intro h0
      have := (hreal x).2 hfpos
      rw [h0, Complex.zero_re] at this
      exact lt_irrefl _ this
    have hval : (∫ h in 𝓕, GlobalTheory.RSnm.rsIntegrand (m₀ + 1) hlt.le F φ φ' (x : ℂ) h ∂μ) /
        ((c : ℂ) * ∫ g in 𝓕₀, (f g : ℂ) * Complex.exp ((x : ℂ) * t g) ∂μ) = P := by
      rw [eU, eq, hsum]
      have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc.ne'
      field_simp
    have hP' : HasProd (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T} => locL (Ideal.absNorm w.1.asIdeal)
        (sat (CG.mk π) w.1) ((sat (CG.mk π') w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ)) P := by
      simp only [← hα, ← hβ]
      exact hP
    simpa only [hval] using hP'

end GlobalTheory.RSnmUnf
