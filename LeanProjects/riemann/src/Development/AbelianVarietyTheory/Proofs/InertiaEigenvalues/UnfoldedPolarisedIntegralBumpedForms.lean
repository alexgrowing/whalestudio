import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CellLintegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralUnipotentCellPosLtTopContinuous
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.NAInterSupSSubset
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSumRankinSelbergSchurTermFinsuppEulerProductStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhitMulLocGLDiagPowOfFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousGlobalWhittakerCoefficientGLAdelesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedIntegrandMeasurableInvariantBoundedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelNatBumpRankinSelbergCellStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ShintaniUnfoldedIntegrandEvalTorusCellStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCellPartUnfoldedIntegralPositiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinsuppVanishingOnEquivComplProdStatement
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate nonZeroDivisors

namespace GlobalTheory.ZEul

theorem unfolded_bump_eq :
∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
  (∀ w ∈ S, ∀ w' : HeightOneSpectrum (𝓞 E), Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal = Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal → w' ∈ S) →
  (∀ w ∉ S, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w) →
  ∀ b : GA E (m + 1) → ℂ, b 1 = 1 → (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) →
  (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ GlobalTheory.JSW.mirS E S m, b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * p ∈ C) →
  ∀ (π π' : CuspSub E (m + 1)) (ω ω' : HChar E), ω.IsUnitary → ω'.IsUnitary → π.HasCentChar ω → π'.HasCentChar ω' →
  ∀ (α α' : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ),
  (∀ w ∉ S, HasSatGL w (π.locRep w) (Finset.univ.val.map (α w))) →
  (∀ w ∉ S, HasSatGL w (π'.locRep w) (Finset.univ.val.map (α' w))) →
  ∀ φ φ' : GA E (m + 1) → ℂ, φ ∈ GlobalTheory.JSW.mspanR π → φ' ∈ GlobalTheory.JSW.mspanR π' →
  (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
      ∀ u ∈ U, ∀ g, φ (g * finGL E (m + 1) u) = φ g) →
  (∀ w ∉ S, ∀ k ∈ KGL w (m + 1), ∀ g, φ (g * finGL E (m + 1) (locGL E (m + 1) w k)) = φ g) → (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
      ∀ u ∈ U, ∀ g, φ' (g * finGL E (m + 1) u) = φ' g) →
  (∀ w ∉ S, ∀ k ∈ KGL w (m + 1), ∀ g, φ' (g * finGL E (m + 1) (locGL E (m + 1) w k)) = φ' g) →
  (∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) → ∀ p ∈ GlobalTheory.JSW.mirS E S m,
      GlobalTheory.JSW.whit φ (p * GlobalTheory.JSW.tl ϖ l) = b p * ∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α w i : ℂ)) (l w)) →
  (∀ (ϖ : ∀ w : HeightOneSpectrum (𝓞 E), (w.adicCompletion E)ˣ), (∀ w, IsUnifV E w (ϖ w : w.adicCompletion E)) →
    ∀ l : HeightOneSpectrum (𝓞 E) →₀ (Fin (m + 1) → ℕ), (∀ w ∈ l.support, w ∉ S) → ∀ p ∈ GlobalTheory.JSW.mirS E S m,
      GlobalTheory.JSW.whit φ' (p * GlobalTheory.JSW.tl ϖ l) = b p * ∏ w ∈ l.support, GlobalTheory.JSW.sphW (qV E w) (fun i => (α' w i : ℂ)) (l w)) →
  φ ≠ 0 ∧ φ' ≠ 0 ∧ ∃ (N : ℕ) (Φ : (Fin (m + 1) → Cinf E) → ℂ), 0 < N ∧ ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧
    tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E (Fin.last m) ∧ (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) ∧
  ∀ (μ : Measure (GA E (m + 1))) [μ.IsHaarMeasure] (𝓕₀ : Set (GA E (m + 1))),
    IsFundamentalDomain (GlobalTheory.CellDec.NE E (m + 1)) 𝓕₀ μ →
   ∃ f t : GA E (m + 1) → ℝ, Measurable f ∧ Measurable t ∧ (∀ g, 0 ≤ f g) ∧ IntegrableOn f 𝓕₀ μ ∧
    0 < ∫ g in 𝓕₀, f g ∂μ ∧ (∃ R : ℝ, ∀ g, f g ≠ 0 → |t g| ≤ R) ∧
   ∀ x : ℝ, 1 < x →
     GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => Ideal.absNorm w.1.asIdeal) (fun w i => (α w.1 i : ℂ)) x ≠ ⊤ →
     GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => Ideal.absNorm w.1.asIdeal) (fun w i => (α' w.1 i : ℂ)) x ≠ ⊤ →
     ∫⁻ g in 𝓕₀, ‖GlobalTheory.ZEul.uInt φ φ Φ N x g‖ₑ ∂μ ≠ ⊤ ∧ ∫⁻ g in 𝓕₀, ‖GlobalTheory.ZEul.uInt φ' φ' Φ N x g‖ₑ ∂μ ≠ ⊤ ∧
     ∫ g in 𝓕₀, GlobalTheory.ZEul.uInt φ φ' Φ N x g ∂μ = (∫ g in 𝓕₀, (f g : ℂ) * Complex.exp (x * t g) ∂μ) * (∑' l : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} →₀ (Fin (m + 1) → ℤ), l.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.1.asIdeal) (fun i => (α w.1 i : ℂ)) (fun i => (α' w.1 i : ℂ)) x v) ∧
     ∫ g in 𝓕₀, GlobalTheory.ZEul.uInt φ φ Φ N x g ∂μ = (∫ g in 𝓕₀, (f g : ℂ) * Complex.exp (x * t g) ∂μ) * (∑' l : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} →₀ (Fin (m + 1) → ℤ), l.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.1.asIdeal) (fun i => (α w.1 i : ℂ)) (fun i => (α w.1 i : ℂ)) x v) ∧
     ∫ g in 𝓕₀, GlobalTheory.ZEul.uInt φ' φ' Φ N x g ∂μ = (∫ g in 𝓕₀, (f g : ℂ) * Complex.exp (x * t g) ∂μ) * (∑' l : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} →₀ (Fin (m + 1) → ℤ), l.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.1.asIdeal) (fun i => (α' w.1 i : ℂ)) (fun i => (α' w.1 i : ℂ)) x v) := by
  intro E _ _ _ m S hsat hψ b hb1 hbN hbC π π' ω ω' hω hω' hπ hπ' α α' hα hα' φ φ' hφ hφ' hU hK hU' hK' hsh hsh'
  classical
  have hϖex : ∀ w : HeightOneSpectrum (𝓞 E), ∃ ϖ : (w.adicCompletion E)ˣ, IsUnifV E w (ϖ : w.adicCompletion E) := by
    intro w
    obtain ⟨ϖ, hϖ⟩ : ∃ ϖ, IsUnifV E w ϖ := ⟨_, Formalism.L2.Host.unif_spec w⟩
    refine ⟨Units.mk0 ϖ fun h => ?_, hϖ⟩
    rw [IsUnifV, h] at hϖ
    simp at hϖ
  choose ϖ hϖ using hϖex
  have hreg : ∀ {ρ : CuspSub E (m + 1)} {ν : HChar E}, ν.IsUnitary → ρ.HasCentChar ν → ∀ F ∈ GlobalTheory.JSW.mspanR ρ,
      GlobalTheory.JSW.IsBCC F := by
    intro ρ ν hν hρ F hF
    obtain ⟨ψ, rfl, h⟩ := GlobalTheory.JSW.mspanR_words GlobalTheory.CuspOrth.cuspFormsBounded ⟨ν, hν, CuspSub.hasCentral_iff.2 hρ⟩ F hF
    have h0 := (h []).2
    rwa [GlobalTheory.JSW.word_nil] at h0
  have hc := hreg hω hπ φ hφ
  have hc' := hreg hω' hπ' φ' hφ'
  have hW : ∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, GlobalTheory.JSW.whit φ (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ g :=
    fun u hu g => GlobalTheory.JSW.WhitModel.whit_mul hc.cont (fun γ g => hc.left γ g) hu g
  have hW' : ∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, GlobalTheory.JSW.whit φ' (u * g) = GlobalTheory.JSW.psiN u * GlobalTheory.JSW.whit φ' g :=
    fun u hu g => GlobalTheory.JSW.WhitModel.whit_mul hc'.cont (fun γ g => hc'.left γ g) hu g
  have hWc := GlobalTheory.T.continuous_globalWhittakerCoefficientGLAdeles E (m + 1) φ hc.cont hc.bdd
  have hWc' := GlobalTheory.T.continuous_globalWhittakerCoefficientGLAdeles E (m + 1) φ' hc'.cont hc'.bdd
  obtain ⟨U, hUo, hUi⟩ := hU
  obtain ⟨U', hUo', hUi'⟩ := hU'
  let stab : (GA E (m + 1) → ℂ) → Subgroup (GL (Fin (m + 1)) (Af E)) := fun F =>
    { carrier := {k | ∀ g, F (g * finGL E (m + 1) k) = F g}
      mul_mem' := fun {a c} ha hc g => by rw [map_mul, ← mul_assoc, hc, ha]
      one_mem' := fun g => by rw [map_one, mul_one]
      inv_mem' := fun {a} ha g => by
        rw [← ha (g * finGL E (m + 1) a⁻¹), mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one] }
  let V : Subgroup (GL (Fin (m + 1)) (Af E)) := (U ⊓ U') ⊔ Subgroup.closure
    {k | ∃ w ∉ S, ∃ k' ∈ KGL w (m + 1), locGL E (m + 1) w k' = k}
  have hVle : ∀ F : GA E (m + 1) → ℂ, (∀ u ∈ U ⊓ U', ∀ g, F (g * finGL E (m + 1) u) = F g) →
      (∀ w ∉ S, ∀ k ∈ KGL w (m + 1), ∀ g, F (g * finGL E (m + 1) (locGL E (m + 1) w k)) = F g) → V ≤ stab F := by
    intro F h1 h2
    refine sup_le (fun k hk => h1 k hk) (Subgroup.closure_le _ |>.2 ?_)
    rintro _ ⟨w, hw, k, hk, rfl⟩
    exact h2 w hw k hk
  have hVφ := hVle φ (fun u hu => hUi u hu.1) hK
  have hVφ' := hVle φ' (fun u hu => hUi' u hu.2) hK'
  have hVo : IsOpen (V : Set (GL (Fin (m + 1)) (Af E))) :=
    Subgroup.isOpen_mono (le_sup_left : U ⊓ U' ≤ V) (by rw [Subgroup.coe_inf]; exact hUo.inter hUo')
  have hVK : ∀ w ∉ S, ∀ k ∈ KGL w (m + 1), locGL E (m + 1) w k ∈ V := fun w hw k hk =>
    (le_sup_right : Subgroup.closure _ ≤ V) (Subgroup.subset_closure ⟨w, hw, k, hk, rfl⟩)
  obtain ⟨N, J, Φ, hN, hΦs, hΦc, hΦt, hΦr, hΦe, hJ, hJV, hn1, hn2, hn3⟩ := GlobalTheory.T.exists_level_nat_bump_rankinSelbergCell E m S hsat V hVo hVK
  have hWJ : ∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g,
      GlobalTheory.JSW.whit φ (g * finGL E (m + 1) κ) = GlobalTheory.JSW.whit φ g := by
    intro κ hκ g
    have e : (fun z => φ (z * finGL E (m + 1) κ)) = φ := funext fun z => hVφ (hJV hκ) z
    rw [GlobalTheory.JSW.whit_mul_right, e]
  have hWJ' : ∀ κ ∈ GlobalTheory.RSLocalPart.levelAt (m + 1) S J, ∀ g,
      GlobalTheory.JSW.whit φ' (g * finGL E (m + 1) κ) = GlobalTheory.JSW.whit φ' g := by
    intro κ hκ g
    have e : (fun z => φ' (z * finGL E (m + 1) κ)) = φ' := funext fun z => hVφ' (hJV hκ) z
    rw [GlobalTheory.JSW.whit_mul_right, e]
  have hb0 : ∀ p ∈ GlobalTheory.JSW.mirS E S m, GlobalTheory.JSW.whit φ p = b p := by
    intro p hp
    simpa [GlobalTheory.JSW.tl] using hsh ϖ hϖ 0 (by simp) p hp
  have hb0' : ∀ p ∈ GlobalTheory.JSW.mirS E S m, GlobalTheory.JSW.whit φ' p = b p := by
    intro p hp
    simpa [GlobalTheory.JSW.tl] using hsh' ϖ hϖ 0 (by simp) p hp
  have h1mem : (1 : GA E (m + 1)) ∈ GlobalTheory.JSW.mirS E S m :=
    ⟨fun w _ => map_one _, fun j => by simp [Matrix.one_apply, eq_comm]⟩
  have hne : ∀ F : GA E (m + 1) → ℂ, GlobalTheory.JSW.whit F 1 = 1 → F ≠ 0 := by
    rintro F h rfl
    simp [GlobalTheory.JSW.whit, GroundTheory.Automorphic.FourierWhittaker.whittaker] at h
  refine ⟨hne φ (by rw [hb0 1 h1mem, hb1]), hne φ' (by rw [hb0' 1 h1mem, hb1]), N, Φ, hN, hΦs, hΦc, hΦt, hΦr, ?_⟩
  intro μ _ 𝓕₀ h𝓕
  obtain ⟨f, t, hfm, htm, hf0, hfi, hfpos, hR, hfC, hfu, hdet⟩ := GlobalTheory.T.exists_cellPart_unfoldedIntegral_positive E m S b φ N J Φ hN hJ hn2
    hΦs.continuous hΦc hΦt hΦr hΦe hWc hW hWJ hb1 hbC hb0 μ 𝓕₀ h𝓕
  refine ⟨f, t, hfm, htm, hf0, hfi, hfpos, hR, ?_⟩
  intro x hx hd hd'
  have ev := GlobalTheory.T.shintani_unfoldedIntegrand_eval_torusCell E m S hψ ϖ hϖ b α α' φ φ' N J Φ hJ hn1 hn2 hn3 hΦt hW hW' hWJ hWJ' (hsh ϖ hϖ) (hsh' ϖ hϖ) x
  have ev1 := GlobalTheory.T.shintani_unfoldedIntegrand_eval_torusCell E m S hψ ϖ hϖ b α α φ φ N J Φ hJ hn1 hn2 hn3 hΦt hW hW hWJ hWJ (hsh ϖ hϖ) (hsh ϖ hϖ) x
  have ev2 := GlobalTheory.T.shintani_unfoldedIntegrand_eval_torusCell E m S hψ ϖ hϖ b α' α' φ' φ' N J Φ hJ hn1 hn2 hn3 hΦt hW' hW' hWJ' hWJ' (hsh' ϖ hϖ)
    (hsh' ϖ hϖ) x
  have hC0 : MeasurableSet (GlobalTheory.CellDec.C0 E (m + 1) S) := (GlobalTheory.T.isOpen_C0 E (m + 1) S).measurableSet
  set I : ℂ := ∫ g in 𝓕₀, (f g : ℂ) * Complex.exp (x * t g) ∂μ with hI
  have hIC : ∫ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, (f g : ℂ) * Complex.exp (x * t g) ∂μ = I := by
    rw [hI, Set.inter_comm, ← Measure.restrict_restrict hC0, ← integral_indicator hC0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    by_cases hg : g ∈ GlobalTheory.CellDec.C0 E (m + 1) S
    · rw [Set.indicator_of_mem hg]
    · rw [Set.indicator_of_notMem hg]; simp [hfC g hg]
  obtain ⟨R, hR'⟩ := hR
  have hfe : IntegrableOn (fun g => (f g : ℂ) * Complex.exp (x * t g)) 𝓕₀ μ := by
    refine Integrable.mono' (hfi.mul_const (Real.exp (|x| * R))) ?_ (Filter.Eventually.of_forall fun g => ?_)
    · exact ((Complex.measurable_ofReal.comp hfm).mul (Complex.measurable_exp.comp
        (measurable_const.mul (Complex.measurable_ofReal.comp htm)))).aestronglyMeasurable
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hf0 g)]
      by_cases h0 : f g = 0
      · simp [h0]
      · refine mul_le_mul_of_nonneg_left ?_ (hf0 g)
        rw [show (x : ℂ) * (t g : ℂ) = ((x * t g : ℝ) : ℂ) by push_cast; ring, Complex.norm_exp_ofReal]
        exact Real.exp_le_exp.2 ((le_abs_self _).trans
          (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hR' g h0) (abs_nonneg x)))
  have hA : ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, ‖(f g : ℂ) * Complex.exp (x * t g)‖ₑ ∂μ ≠ ⊤ :=
    (hfe.mono_set Set.inter_subset_left).2.ne
  have key : ∀ (B : GA E (m + 1) → ℂ) (P : GlobalTheory.CellDec.abelian₂ E (m + 1) S → ℂ),
      (∀ g ∈ GlobalTheory.CellDec.C0 E (m + 1) S, ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) S,
        (GlobalTheory.CellDec.dinv (m + 1) l.1 : ℂ) * B (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) =
          P l * ((f g : ℂ) * Complex.exp (x * t g))) →
      (∀ l, (GlobalTheory.CellDec.dinv (m + 1) l.1 : ℂ) *
        ∫ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, B (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) ∂μ = P l * I) ∧
      (∀ l, ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l.1) *
        ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, ‖B (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g)‖ₑ ∂μ =
        ‖P l‖ₑ * ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, ‖(f g : ℂ) * Complex.exp (x * t g)‖ₑ ∂μ) := by
    intro B P hB
    have hs : NullMeasurableSet (𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S) μ :=
      h𝓕.nullMeasurableSet.inter hC0.nullMeasurableSet
    have hae : ∀ l : GlobalTheory.CellDec.abelian₂ E (m + 1) S, ∀ᵐ g ∂μ.restrict (𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S),
        (GlobalTheory.CellDec.dinv (m + 1) l.1 : ℂ) * B (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) =
          P l * ((f g : ℂ) * Complex.exp (x * t g)) :=
      fun l => (ae_restrict_mem₀ hs).mono fun g hg => hB g hg.2 l
    refine ⟨fun l => ?_, fun l => ?_⟩
    · rw [← integral_const_mul, integral_congr_ae (hae l), integral_const_mul, hIC]
    · have hpos : 0 < GlobalTheory.CellDec.dinv (m + 1) l.1 :=
        Finset.prod_pos fun v _ => zpow_pos (by exact_mod_cast (GlobalTheory.LFun.qV_ne_zero v).bot_lt) _
      have hd : ‖(GlobalTheory.CellDec.dinv (m + 1) l.1 : ℂ)‖ₑ = ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l.1) := by
        rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg hpos.le]
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_const_mul' _ _ enorm_ne_top]
      refine lintegral_congr_ae ((hae l).mono fun g hg => ?_)
      dsimp only
      rw [← hd, ← enorm_mul, hg, enorm_mul]
  have k12 := key (GlobalTheory.ZEul.uInt φ φ' Φ N x) (fun l => l.1.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal)
      (fun i => (α w i : ℂ)) (fun i => (α' w i : ℂ)) x v) (fun g hg l => by
    rw [(ev g hg).2.2 l, hfu g hg, hdet, mul_assoc])
  have k11 := key (GlobalTheory.ZEul.uInt φ φ Φ N x) (fun l => l.1.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal)
      (fun i => (α w i : ℂ)) (fun i => (α w i : ℂ)) x v) (fun g hg l => by
    rw [(ev1 g hg).2.2 l, hfu g hg, hdet, mul_assoc])
  have k22 := key (GlobalTheory.ZEul.uInt φ' φ' Φ N x) (fun l => l.1.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal)
      (fun i => (α' w i : ℂ)) (fun i => (α' w i : ℂ)) x v) (fun g hg l => by
    rw [(ev2 g hg).2.2 l, (ev g hg).2.1, hfu g hg, hdet, mul_assoc])
  obtain ⟨hm11, hinv11, -⟩ := GlobalTheory.T.unfoldedIntegrand_measurable_invariant_bounded E m φ φ Φ N x hWc hWc hW hW hΦs.continuous hΦr
  obtain ⟨hm22, hinv22, -⟩ := GlobalTheory.T.unfoldedIntegrand_measurable_invariant_bounded E m φ' φ' Φ N x hWc' hWc' hW' hW' hΦs.continuous hΦr
  obtain ⟨hm12, hinv12, hbd⟩ := GlobalTheory.T.unfoldedIntegrand_measurable_invariant_bounded E m φ φ' Φ N x hWc hWc' hW hW' hΦs.continuous hΦr
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_equiv_finsupp_compl_prod_eq S (m + 1)
  have hq : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S}, 2 ≤ Ideal.absNorm w.1.asIdeal := fun w => by
    have h1 : Ideal.absNorm w.1.asIdeal ≠ 1 := fun h => w.1.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
    have h0 : Ideal.absNorm w.1.asIdeal ≠ 0 := fun h => w.1.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
    omega
  have hsum : ∀ a : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ,
      GlobalTheory.RSPole.eulD (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => Ideal.absNorm w.1.asIdeal)
        (fun w i => (a w.1 i : ℂ)) x ≠ ⊤ →
      (∑' l : GlobalTheory.CellDec.abelian₂ E (m + 1) S, ‖l.1.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal)
        (fun i => (a w i : ℂ)) (fun i => (a w i : ℂ)) x v‖ₑ) ≠ ⊤ := by
    intro a ha
    have hs := (GlobalTheory.T.hasSum_rankinSelbergSchurTerm_finsupp_eulerProduct (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => Ideal.absNorm w.1.asIdeal)
      (fun w => a w.1) (fun w => a w.1) x hx hq ha ha).summable
    have h2 := e.summable_iff.2 hs
    have h3 : (fun l' => (fun l : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} →₀ (Fin (m + 1) → ℤ) => l.prod fun w v =>
        GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.1.asIdeal) (fun j => (a w.1 j : ℂ)) (fun j => (a w.1 j : ℂ)) x v) (e l')) =
        fun l : GlobalTheory.CellDec.abelian₂ E (m + 1) S => l.1.prod fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal)
          (fun i => (a w i : ℂ)) (fun i => (a w i : ℂ)) x v :=
      funext fun l => he ℂ (fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal) (fun i => (a w i : ℂ))
        (fun i => (a w i : ℂ)) x v) (fun i => GlobalTheory.ZEul.rsTerm_zero _ _ _ _) l
    rw [Function.comp_def, h3] at h2
    have h4 := summable_norm_iff.2 h2
    have h5 : Summable fun l : GlobalTheory.CellDec.abelian₂ E (m + 1) S => ‖l.1.prod fun w v => GlobalTheory.ZEul.rsTerm
        (Ideal.absNorm w.asIdeal) (fun i => (a w i : ℂ)) (fun i => (a w i : ℂ)) x v‖₊ :=
      NNReal.summable_coe.1 (by simpa using h4)
    simpa [enorm_eq_nnnorm] using ENNReal.tsum_coe_ne_top_iff_summable.2 h5
  have hlin : ∀ (B : GA E (m + 1) → ℂ) (P : GlobalTheory.CellDec.abelian₂ E (m + 1) S → ℂ), Measurable B →
      (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, B (u * g) = B g) →
      (∀ l, ENNReal.ofReal (GlobalTheory.CellDec.dinv (m + 1) l.1) *
        ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, ‖B (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g)‖ₑ ∂μ =
        ‖P l‖ₑ * ∫⁻ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, ‖(f g : ℂ) * Complex.exp (x * t g)‖ₑ ∂μ) →
      (∑' l, ‖P l‖ₑ) ≠ ⊤ → ∫⁻ g in 𝓕₀, ‖B g‖ₑ ∂μ ≠ ⊤ := by
    intro B P hBm hBi hl hP
    rw [GlobalTheory.CellDec.cell_lintegral μ S ϖ hϖ 𝓕₀ h𝓕 (fun g => ‖B g‖ₑ) hBm.enorm
      (fun u hu g => by simp only [hBi u hu g])]
    simp_rw [hl, ENNReal.tsum_mul_right]
    exact ENNReal.mul_ne_top hP hA
  have liftZP_unit := hlin _ _ hm11 hinv11 k11.2 (hsum α hd)
  have lix_inf_of_locP_le := hlin _ _ hm22 hinv22 k22.2 (hsum α' hd')
  have i11 : Integrable (GlobalTheory.ZEul.uInt φ φ Φ N x) (μ.restrict 𝓕₀) := ⟨hm11.aestronglyMeasurable, liftZP_unit.lt_top⟩
  have i22 : Integrable (GlobalTheory.ZEul.uInt φ' φ' Φ N x) (μ.restrict 𝓕₀) := ⟨hm22.aestronglyMeasurable, lix_inf_of_locP_le.lt_top⟩
  have i12 : Integrable (GlobalTheory.ZEul.uInt φ φ' Φ N x) (μ.restrict 𝓕₀) :=
    Integrable.mono' ((i11.norm.add i22.norm).div_const 2) hm12.aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => hbd g)
  have hbo : ∀ (B : GA E (m + 1) → ℂ) (P : GlobalTheory.CellDec.abelian₂ E (m + 1) S → ℂ), Measurable B →
      Integrable B (μ.restrict 𝓕₀) → (∀ u ∈ GlobalTheory.CellDec.NA E (m + 1), ∀ g, B (u * g) = B g) →
      (∀ l, (GlobalTheory.CellDec.dinv (m + 1) l.1 : ℂ) *
        ∫ g in 𝓕₀ ∩ GlobalTheory.CellDec.C0 E (m + 1) S, B (GlobalTheory.CellDec.tl (m + 1) ϖ l.1 * g) ∂μ = P l * I) →
      ∫ g in 𝓕₀, B g ∂μ = I * ∑' l, P l := by
    intro B P hBm hBi hBinv hl
    have h := (GlobalTheory.CellDec.cell_integral μ S ϖ hϖ 𝓕₀ h𝓕 B hBm hBi hBinv).2
    simp_rw [hl] at h
    rw [← h.tsum_eq, tsum_mul_right, mul_comm]
  have hre : ∀ a c : HeightOneSpectrum (𝓞 E) → Fin (m + 1) → ℂˣ,
      ∑' l : GlobalTheory.CellDec.abelian₂ E (m + 1) S, l.1.prod (fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal)
        (fun i => (a w i : ℂ)) (fun i => (c w i : ℂ)) x v) =
      ∑' l : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} →₀ (Fin (m + 1) → ℤ), l.prod fun w v =>
        GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.1.asIdeal) (fun i => (a w.1 i : ℂ)) (fun i => (c w.1 i : ℂ)) x v := by
    intro a c
    rw [← e.tsum_eq]
    exact tsum_congr fun l => (he ℂ (fun w v => GlobalTheory.ZEul.rsTerm (Ideal.absNorm w.asIdeal) (fun i => (a w i : ℂ))
      (fun i => (c w i : ℂ)) x v) (fun i => GlobalTheory.ZEul.rsTerm_zero _ _ _ _) l).symm
  refine ⟨liftZP_unit, lix_inf_of_locP_le, ?_, ?_, ?_⟩
  · rw [hbo _ _ hm12 i12 hinv12 k12.1, hre]
  · rw [hbo _ _ hm11 i11 hinv11 k11.1, hre]
  · rw [hbo _ _ hm22 i22 hinv22 k22.1, hre]

end GlobalTheory.ZEul
