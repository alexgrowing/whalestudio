import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedPolarisedIntegralBumpedForms
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep Formalism.L2.Host Formalism.UG GlobalTheory.LFun
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfolded_polarised_integral_bumped_forms : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))),
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
  first | (exact @GlobalTheory.ZEul.unfolded_bump_eq) | (exact GlobalTheory.ZEul.unfolded_bump_eq) | (intros; apply GlobalTheory.ZEul.unfolded_bump_eq  <;> assumption)
