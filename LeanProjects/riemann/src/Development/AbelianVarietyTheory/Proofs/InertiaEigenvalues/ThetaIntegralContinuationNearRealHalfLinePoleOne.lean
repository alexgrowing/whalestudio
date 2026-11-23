import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNormRsHatLeConst
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIntegralUpperMspan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousIntegralOfCompact
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetIntegralRsHatZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergThetaIntegralPoleRapidKernelSpanStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergKernelZeroCoeffTwoCentralCharsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFundamentalDomainDetShellLatticeGLStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralAbsDetCpowBoundedShellEntireStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralDetLeOneEqGeometricSeriesShellsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAnalyticSubOneDivOneSubUnitMulExpStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors ComplexConjugate

noncomputable section
namespace GlobalTheory.RSThetaCont
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem mem_bddForms_of_mspanR {π : CuspSub E a} {ω : HChar E} (hω : ω.IsUnitary) (hπ : π.HasCentChar ω) {φ : Sm E a}
    (hφ : φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π) : φ.1 ∈ GlobalTheory.Petersson.bddForms E a ω := by
  have hc0 := CuspSub.hasCentral_iff.2 hπ
  have hu : π.IsUnitary := ⟨ω, hω, hc0⟩
  have hR : φ.1 ∈ GlobalTheory.JSW.mspanR π := hφ.elim (fun h => GlobalTheory.JSW.mem_mspanR_of_mem h) id
  obtain ⟨ψ, hψ, h⟩ := GlobalTheory.JSW.mspanR_words GlobalTheory.CuspOrth.cuspFormsBounded hu φ.1 hR
  have h0 := (h []).2
  rw [GlobalTheory.JSW.word_nil, hψ] at h0
  have hR' : φ.1 ∈ GlobalTheory.JSW.rspan π := (GlobalTheory.JSW.rspan_eq_mspanR π).symm ▸ hR
  have hZ : GlobalTheory.JSW.rspan π ≤ GlobalTheory.JSW.Central.centralFns E a ω := by
    refine GlobalTheory.JSW.rspan_le (fun ψ hψ z g => hc0.apply hψ z g) (fun F hF h z g => ?_) fun F hF X _ ν _ k γ _ z g => ?_
    · change F (GeneralLinearGroup.scalar (Fin a) z * g * h) = _ * F (g * h)
      rw [mul_assoc]; exact hF z _
    · change GlobalTheory.JSW.kerInf ν k γ F (GeneralLinearGroup.scalar (Fin a) z * g) = _ * GlobalTheory.JSW.kerInf ν k γ F g
      simp only [GlobalTheory.JSW.kerInf, mul_assoc]
      rw [← integral_const_mul]
      congr 1
      funext x
      rw [hF z]; ring
  exact ⟨h0.cont, GlobalTheory.JSW.rspan_left π hR', hZ hR', h0.bdd⟩

theorem resFn_props {ω ω' : HChar E} (hω : ω.IsUnitary) (hω' : ω'.IsUnitary) {φ φ' : Sm E a}
    (h : φ.1 ∈ GlobalTheory.Petersson.bddForms E a ω) (h' : φ'.1 ∈ GlobalTheory.Petersson.bddForms E a ω')
    {ℓ : Fin a} {Φ : (Fin a → Cinf E) → ℂ} (hΦ : GlobalTheory.CuspQuot.IsTest (GlobalTheory.RSTheta.rowSet E ℓ) Φ)
    (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) :
    Continuous (fun g => GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0) ∧
    (∃ C : ℝ, ∀ g, ‖GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0‖ ≤ C) ∧
    (∀ (γ : GL (Fin a) E) (g : GA E a), GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η (ratGL E a γ * g) 0 =
      GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0) ∧
    ∀ (z : Neutral.B1.Ideles E) (g : GA E a),
      GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η (GeneralLinearGroup.scalar (Fin a) z * g) 0 =
        ((ω.1 z : ℂˣ) : ℂ) * starRingEnd ℂ ((ω'.1 z : ℂˣ) : ℂ) * GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0 := by
  exact GlobalTheory.T.rankinSelberg_kernel_zero_coeff_two_central_chars E a ω ω' hω hω' φ φ' h h' ℓ Φ hΦ J η

theorem isFundamentalDomain_shell (ha : 0 < a) (μ : Measure (GA E a)) [μ.IsHaarMeasure] {𝓕 : Set (GA E a)}
    (h𝓕 : IsFundamentalDomain (ratGL E a).range 𝓕 μ) :
    IsFundamentalDomain (latticeGL E a) (𝓕 ∩ {g | Real.exp (-((a : ℝ) * (Module.finrank ℚ E : ℝ))) <
      (ideleModule E (GeneralLinearGroup.det g) : ℝ) ∧ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}) μ := by
  exact GlobalTheory.T.isFundamentalDomain_det_shell_latticeGL E a ha μ 𝓕 h𝓕

theorem differentiable_setIntegral_cpow (μ : Measure (GA E a)) {S : Set (GA E a)} (hSm : NullMeasurableSet S μ) (hS : μ S < ⊤) {c : ℝ} (hc : 0 < c)
    (hδ : ∀ g ∈ S, c ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ∧ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1)
    {F : GA E a → ℂ} (hF : Continuous F) {C : ℝ} (hC : ∀ g, ‖F g‖ ≤ C) :
    Differentiable ℂ fun s : ℂ => ∫ g in S, F g * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) ∂μ := by
  exact GlobalTheory.T.integral_absDet_cpow_bounded_shell_entire E a μ S hSm hS c hc hδ F hF C hC

theorem integral_low_geometric (ha : 0 < a) (μ : Measure (GA E a)) [μ.IsHaarMeasure] {𝓕 : Set (GA E a)}
    (h𝓕 : IsFundamentalDomain (ratGL E a).range 𝓕 μ) {F : GA E a → ℂ} (hF : Continuous F) {C : ℝ}
    (hC : ∀ g, ‖F g‖ ≤ C) (hrat : ∀ (γ : GL (Fin a) E) (g : GA E a), F (ratGL E a γ * g) = F g) {χ : ℂ}
    (hχ : ‖χ‖ = 1) (hz : ∀ g, F (splitCentre E a 1 * g) = χ * F g) {s : ℂ} (hs : 1 < s.re) :
    ∫ g in 𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1},
        F g * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) ∂μ =
      (∫ g in 𝓕 ∩ {g | Real.exp (-((a : ℝ) * (Module.finrank ℚ E : ℝ))) <
          (ideleModule E (GeneralLinearGroup.det g) : ℝ) ∧ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1},
        F g * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) ∂μ) /
      (1 - starRingEnd ℂ χ * Complex.exp (-((((a : ℝ) * (Module.finrank ℚ E : ℝ) : ℝ) : ℂ) * (s - 1)))) := by
  exact GlobalTheory.T.integral_det_le_one_eq_geometric_series_shells E a ha μ 𝓕 h𝓕 F hF C hC hrat χ hχ hz s hs

theorem exists_analytic_ratio {L : ℝ} (hL : 0 < L) (χ : ℂ) (hχ : ‖χ‖ = 1) : ∃ h : ℂ → ℂ,
    (∀ x : ℝ, 0 < x → AnalyticAt ℂ h (x : ℂ)) ∧
    (∀ x : ℝ, 1 < x → h (x : ℂ) = ((x : ℂ) - 1) / (1 - χ * Complex.exp (-((L : ℂ) * ((x : ℂ) - 1))))) ∧
    (χ ≠ 1 → h 1 = 0) := by
  exact GlobalTheory.T.exists_analytic_sub_one_div_one_sub_mul_exp L hL χ hχ

theorem setIntegral_eq_zero_of_scalar (μ : Measure (GA E a)) [μ.IsHaarMeasure] {S : Set (GA E a)}
    (hS : IsFundamentalDomain (latticeGL E a) S μ) {F : GA E a → ℂ} (hinv : ∀ γ ∈ latticeGL E a, ∀ g, F (γ * g) = F g)
    (z : Neutral.B1.Ideles E) {ν : ℂ} (hν : ν ≠ 1) (hz : ∀ g, F (GeneralLinearGroup.scalar (Fin a) z * g) = ν * F g) :
    ∫ g in S, F g ∂μ = 0 := by
  have h1 := GlobalTheory.RSResidue.setIntegral_mul_right hS hinv (GeneralLinearGroup.scalar (Fin a) z)
  have e : ∀ g, F (g * GeneralLinearGroup.scalar (Fin a) z) = ν * F g := fun g => by
    rw [← hz g]
    congr 1
    exact Units.ext (Matrix.scalar_commute _ (fun _ => Commute.all _ _) g.val).eq.symm
  simp only [e, integral_const_mul] at h1
  have h2 : (ν - 1) * ∫ g in S, F g ∂μ = 0 := by rw [sub_mul, h1, one_mul, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hν)

open GlobalTheory.CuspRep.CuspidalL2GL in

theorem theta_integral_continuation : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ℓ : Fin a) (Φ : (Fin a → Cinf E) → ℂ), ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ → ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 𝓕' : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (latticeGL E a) 𝓕' μ → ∃ c : ℂ, ((∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) → Φ ≠ 0 → c ≠ 0) ∧ ∀ (π π' : CuspSub E a) (ω ω' : HChar E), ω.IsUnitary → ω'.IsUnitary → π.HasCentChar ω → π'.HasCentChar ω' → ∀ φ φ' : Sm E a, (φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspanR π) → (φ' ∈ π'.V ∨ φ'.1 ∈ GlobalTheory.JSW.mspanR π') → ∃ F : ℂ → ℂ, (∀ x : ℝ, 0 < x → AnalyticAt ℂ F (x : ℂ)) ∧ (∀ x : ℝ, 1 < x → F (x : ℂ) = ((x - 1 : ℝ) : ℂ) * ∫ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ) ∂μ) ∧ (ω = ω' → F 1 = c * ∫ g in 𝓕', φ.1 g * starRingEnd ℂ (φ'.1 g) ∂μ) ∧ (ω ≠ ω' → F 1 = 0) := by
  intro E _ _ _ a ℓ Φ hΦ hcs hs J η μ _ 𝓕 𝓕' h𝓕 h𝓕'
  obtain ⟨c, hc0, hc⟩ := GlobalTheory.T.rankinSelberg_theta_integral_pole_rapid_kernel_span E a ℓ Φ hΦ hcs hs J η μ 𝓕 𝓕' h𝓕 h𝓕'
  refine ⟨c, hc0, ?_⟩
  intro π π' ω ω' hω hω' hπ hπ' φ φ' hφ hφ'
  have ha : 0 < a := ℓ.pos
  have hb := mem_bddForms_of_mspanR hω hπ hφ
  have hb' := mem_bddForms_of_mspanR hω' hπ' hφ'
  have hu : π.IsUnitary := ⟨ω, hω, CuspSub.hasCentral_iff.2 hπ⟩
  have hu' : π'.IsUnitary := ⟨ω', hω', CuspSub.hasCentral_iff.2 hπ'⟩
  have hT : GlobalTheory.CuspQuot.IsTest (GlobalTheory.RSTheta.rowSet E ℓ) Φ := ⟨hΦ, hcs, hs⟩
  have hR : φ ∈ GlobalTheory.RSThetaLowM.rsm π :=
    show φ.1 ∈ GlobalTheory.JSW.mspanR π from hφ.elim (fun h => GlobalTheory.JSW.mem_mspanR_of_mem h) id
  have hR' : φ' ∈ GlobalTheory.RSThetaLowM.rsm π' :=
    show φ'.1 ∈ GlobalTheory.JSW.mspanR π' from hφ'.elim (fun h => GlobalTheory.JSW.mem_mspanR_of_mem h) id
  have hδc : Continuous fun g : GA E a => (ideleModule E (GeneralLinearGroup.det g) : ℝ) :=
    GlobalTheory.RSThetaLow.continuous_absDet
  have hδ0 : ∀ g : GA E a, 0 < (ideleModule E (GeneralLinearGroup.det g) : ℝ) := fun g => (ideleModule E _).2
  have hlowm : MeasurableSet {g : GA E a | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1} :=
    (isClosed_le hδc continuous_const).measurableSet
  have hupm : MeasurableSet {g : GA E a | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)} :=
    (isClosed_le continuous_const hδc).measurableSet

  obtain ⟨r1, ⟨C0, r2⟩, r3, r4⟩ := resFn_props hω hω' hb hb' hT J η
  obtain ⟨z0, hz0⟩ : ∃ z0 : Neutral.B1.Ideles E, splitCentre E a 1 = GeneralLinearGroup.scalar (Fin a) z0 :=
    ⟨_, splitCentre_eq_scalar 1⟩
  set χ : ℂ := ((ω.1 z0 : ℂˣ) : ℂ) * starRingEnd ℂ ((ω'.1 z0 : ℂˣ) : ℂ) with hχdef
  have hχ : ‖χ‖ = 1 := by rw [hχdef, norm_mul, Complex.norm_conj, hω z0, hω' z0, one_mul]
  have hzF : ∀ g, GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η (splitCentre E a 1 * g) 0 =
      χ * GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0 := fun g => by rw [hz0]; exact r4 z0 g

  have hS := isFundamentalDomain_shell ha μ h𝓕
  haveI : DiscreteTopology (latticeGL E a) := GlobalTheory.CuspRep.CuspidalL2GL.discreteTopology_latticeGL
  haveI : Countable (latticeGL E a) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  have hSfin := hS
  replace hSfin : μ (𝓕 ∩ {g | Real.exp (-((a : ℝ) * (Module.finrank ℚ E : ℝ))) <
      (ideleModule E (GeneralLinearGroup.det g) : ℝ) ∧ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}) < ⊤ := by
    rw [← GlobalTheory.AutomorphicL2Unitary.quotMeasure_univ hS]; exact measure_lt_top _ _
  have hL : 0 < (a : ℝ) * (Module.finrank ℚ E : ℝ) :=
    mul_pos (Nat.cast_pos.2 ha) (Nat.cast_pos.2 Module.finrank_pos)
  set I : ℂ → ℂ := fun s => ∫ g in 𝓕 ∩ {g | Real.exp (-((a : ℝ) * (Module.finrank ℚ E : ℝ))) <
      (ideleModule E (GeneralLinearGroup.det g) : ℝ) ∧ (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1},
      GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0 * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (s - 1) ∂μ
    with hIdef
  have hI : Differentiable ℂ I := differentiable_setIntegral_cpow μ hS.nullMeasurableSet hSfin (Real.exp_pos _)
    (fun g hg => ⟨hg.2.1.le, hg.2.2⟩) r1 r2
  have hA : ∀ s : ℂ, 1 < s.re → GlobalTheory.RSThetaLow.partA ℓ φ.1 φ'.1 Φ J η μ 𝓕 s = I s /
      (1 - starRingEnd ℂ χ * Complex.exp (-((((a : ℝ) * (Module.finrank ℚ E : ℝ) : ℝ) : ℂ) * (s - 1)))) :=
    fun s hs => integral_low_geometric ha μ h𝓕 r1 r2 r3 hχ hzF hs
  obtain ⟨h, hh1, hh2, hh3⟩ := exists_analytic_ratio hL (starRingEnd ℂ χ) (by rw [Complex.norm_conj]; exact hχ)

  obtain ⟨-, -, u3, u4, -⟩ := GlobalTheory.RSThetaM.theta_integral_upper_mspan E a ℓ π π' hu hu' φ φ' hφ hφ' Φ hΦ.continuous
    hcs hs J η μ 𝓕 h𝓕
  obtain ⟨-, -, b3⟩ := GlobalTheory.RSThetaLowM.partB_entire J η hu hu' hR hR' hb.1 hb'.1 hT h𝓕
  set K0 : ℂ := ∫ g in 𝓕 ∩ {g | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)} ∩
      {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1},
      ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val) ∂μ
    with hK0
  set G : ℂ → ℂ := fun s => (∫ g in 𝓕 ∩ {g | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)},
      (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) *
        ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ s ∂μ) +
      GlobalTheory.RSThetaLow.partB ℓ φ.1 φ'.1 Φ J η μ 𝓕 s - K0 with hGdef
  have hG : Differentiable ℂ G := (u4.add b3).sub_const K0
  have hFan : ∀ x : ℝ, 0 < x → AnalyticAt ℂ (fun s => (s - 1) * G s + I s * h s) (x : ℂ) := fun x hx =>
    ((analyticAt_id.sub analyticAt_const).mul (hG.analyticAt _)).add ((hI.analyticAt _).mul (hh1 x hx))

  have hFeq : ∀ x : ℝ, 1 < x → ((x : ℂ) - 1) * G x + I x * h x = ((x - 1 : ℝ) : ℂ) * ∫ g in 𝓕,
      (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) *
        ((((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ)) : ℂ) ∂μ := by
    intro x hx
    have e1 : ∀ g : GA E a, (((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ (x : ℝ) : ℝ) : ℂ) =
        ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (x : ℂ) := fun g =>
      Complex.ofReal_cpow (hδ0 g).le x
    simp only [e1]
    have hxre : 1 < (x : ℂ).re := by simpa using hx
    have hlow := GlobalTheory.RSThetaLowM.integral_low_eq J η hu hu' hR hR' hb.1 hb'.1 hT h𝓕 hxre
    have etsum : ∀ g, ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g
        ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val) = ∑' ξ : Fin a → E, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g
        ((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val) := fun g =>
      GlobalTheory.RSThetaLow.tsum_rsPsi_eq_tsum_ne_zero J η φ.1 φ'.1 hs g
    have iLo : IntegrableOn (fun g : GA E a => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g
        ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (x : ℂ))
        (𝓕 ∩ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}) μ := by
      simp only [etsum]; exact hlow.1
    have iUp := u3 (x : ℂ)
    have hint : IntegrableOn (fun g : GA E a => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g
        ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) * ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (x : ℂ))
        𝓕 μ := by
      refine (iLo.union iUp).mono_set fun g hg => ?_
      rcases le_total (ideleModule E (GeneralLinearGroup.det g) : ℝ) 1 with h' | h'
      · exact Or.inl ⟨hg, h'⟩
      · exact Or.inr ⟨hg, h'⟩
    have s1 := integral_inter_add_diff hlowm hint
    have s2 := integral_inter_add_diff hlowm iUp
    have eset : (𝓕 ∩ {g : GA E a | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)}) \ {g : GA E a | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1} =
        𝓕 \ {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1} := by
      ext g
      simp only [Set.mem_diff, Set.mem_inter_iff, Set.mem_setOf_eq, not_le]
      exact ⟨fun h' => ⟨h'.1.1, h'.2⟩, fun h' => ⟨⟨h'.1, h'.2.le⟩, h'.2⟩⟩
    rw [eset] at s2
    have sK : ∫ g in 𝓕 ∩ {g : GA E a | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)} ∩
        {g | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1}, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
          GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) *
          ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (x : ℂ) ∂μ = K0 := by
      rw [hK0]
      refine integral_congr_ae ?_
      refine (ae_restrict_of_ae_restrict_of_subset (Set.inter_subset_inter_left _ Set.inter_subset_right) (ae_restrict_mem (hupm.inter hlowm))).mono
        fun g hg => ?_
      have h1 : (ideleModule E (GeneralLinearGroup.det g) : ℝ) = 1 := le_antisymm hg.2 hg.1
      simp only [h1, Complex.ofReal_one, Complex.one_cpow, mul_one]
    have sLo : ∫ g in 𝓕 ∩ {g : GA E a | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1},
        (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g
          ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) *
          ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (x : ℂ) ∂μ =
        GlobalTheory.RSThetaLow.partA ℓ φ.1 φ'.1 Φ J η μ 𝓕 x + GlobalTheory.RSThetaLow.partB ℓ φ.1 φ'.1 Φ J η μ 𝓕 x := by
      simp only [etsum]; exact hlow.2
    rw [← s1, sLo, hA x hxre, hh2 x hx]
    rw [sK] at s2
    have hup : ∫ g in 𝓕 \ {g : GA E a | (ideleModule E (GeneralLinearGroup.det g) : ℝ) ≤ 1},
        (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g
          ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) *
          ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (x : ℂ) ∂μ =
        (∫ g in 𝓕 ∩ {g | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)},
          (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, GlobalTheory.RSTheta.rsPsi ℓ φ.1 φ'.1 Φ J η g
            ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)) *
            ((ideleModule E (GeneralLinearGroup.det g) : ℝ) : ℂ) ^ (x : ℂ) ∂μ) - K0 := by
      rw [← s2]; ring
    rw [hup, hGdef]
    push_cast
    ring
  refine ⟨fun s => (s - 1) * G s + I s * h s, hFan, hFeq, ?_, ?_⟩
  ·
    intro hωω
    subst hωω
    obtain ⟨-, ht⟩ := hc π π' ω hω hπ hπ' φ φ' hφ hφ'
    have hcont : Tendsto (fun x : ℝ => ((x : ℂ) - 1) * G x + I x * h x) (𝓝[>] 1)
        (𝓝 (((1 : ℂ) - 1) * G 1 + I 1 * h 1)) := by
      have h1 := (hFan 1 one_pos).continuousAt.tendsto.comp (Complex.continuous_ofReal.tendsto 1)
      simp only [Complex.ofReal_one] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    refine tendsto_nhds_unique hcont (ht.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with x hx using (hFeq x hx).symm
  ·
    intro hne
    show ((1 : ℂ) - 1) * G 1 + I 1 * h 1 = 0
    rw [sub_self, zero_mul, zero_add]
    by_cases hχ1 : starRingEnd ℂ χ = 1
    · have hχ1' : χ = 1 := by simpa using congrArg (starRingEnd ℂ) hχ1
      obtain ⟨z, hz⟩ : ∃ z, ω.1 z ≠ ω'.1 z := by
        by_contra hall
        push_neg at hall
        exact hne (Subtype.ext (MonoidHom.ext hall))
      have hν : ((ω.1 z : ℂˣ) : ℂ) * starRingEnd ℂ ((ω'.1 z : ℂˣ) : ℂ) ≠ 1 := by
        intro hν1
        apply hz
        refine Units.ext ?_
        have hw : starRingEnd ℂ ((ω'.1 z : ℂˣ) : ℂ) * ((ω'.1 z : ℂˣ) : ℂ) = 1 := by
          rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hω' z]; simp
        calc ((ω.1 z : ℂˣ) : ℂ) = ((ω.1 z : ℂˣ) : ℂ) * (starRingEnd ℂ ((ω'.1 z : ℂˣ) : ℂ) * ((ω'.1 z : ℂˣ) : ℂ)) := by
              rw [hw, mul_one]
          _ = (((ω.1 z : ℂˣ) : ℂ) * starRingEnd ℂ ((ω'.1 z : ℂˣ) : ℂ)) * ((ω'.1 z : ℂˣ) : ℂ) := by ring
          _ = ((ω'.1 z : ℂˣ) : ℂ) := by rw [hν1, one_mul]
      have hzp : ∀ (n : ℤ) (g : GA E a), GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η (splitCentre E a 1 ^ n * g) 0 =
          GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0 := by
        intro n
        refine Int.induction_on n ?_ ?_ ?_
        · intro g; rw [zpow_zero, one_mul]
        · intro k ih g
          rw [_root_.zpow_add_one, mul_assoc, ih, hzF, hχ1', one_mul]
        · intro k ih g
          rw [_root_.zpow_sub_one, mul_assoc, ih]
          have := hzF ((splitCentre E a 1)⁻¹ * g)
          rw [← mul_assoc, mul_inv_cancel, one_mul, hχ1', one_mul] at this
          exact this.symm
      have hinv : ∀ γ ∈ latticeGL E a, ∀ g, GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η (γ * g) 0 =
          GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0 := by
        intro γ hγ g
        obtain ⟨γ', n, rfl⟩ := mem_latticeGL_iff.1 hγ
        rw [mul_assoc, r3, hzp]
      have h0 := setIntegral_eq_zero_of_scalar μ hS (F := fun g => GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0) hinv z hν (r4 z)
      have hI1 : I 1 = 0 := by
        rw [hIdef]
        simp only [sub_self, Complex.cpow_zero, mul_one]
        exact h0
      rw [hI1, zero_mul]
    · rw [hh3 hχ1, mul_zero]

end GlobalTheory.RSThetaCont
