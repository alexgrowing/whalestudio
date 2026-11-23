import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsUnitaryOfCharIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivariantProj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIntegralUpperMspan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNormRsHatLeConst

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped ENNReal nonZeroDivisors ComplexConjugate
open GlobalTheory.ThetaPoisson GlobalTheory.RSTheta

namespace GlobalTheory.RSThetaSelf

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem rsPsi_self_eq_norm (ℓ : Fin a) (F : GA E a → ℂ) {Φ : (Fin a → Cinf E) → ℂ}
    (hΦ : ∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (g : GA E a)
    (y : Fin a → Ad E) : rsPsi ℓ F F Φ J η g y = ((‖rsPsi ℓ F F Φ J η g y‖ : ℝ) : ℂ) := by
  have key : ∀ z w t : ℂ, 0 ≤ w.re → w.im = 0 → (t = 0 ∨ t = 1) →
      z * conj z * w * t = ((‖z * conj z * w * t‖ : ℝ) : ℂ) := by
    intro z w t h1 h2 ht
    have hw : w = ((w.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [h2])
    rcases ht with rfl | rfl
    · simp
    · rw [mul_one, Complex.mul_conj, hw, ← Complex.ofReal_mul, Complex.norm_real,
        Real.norm_of_nonneg (mul_nonneg (Complex.normSq_nonneg z) h1)]
  simp only [rsPsi, thetaFn, rsInf]
  refine key _ _ _ (hΦ _).1 (hΦ _).2 ?_
  by_cases h : (fun i => pFin E (y i)) - η ∈ latt a J <;> simp [h]

theorem lintegral_ne_top : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ℓ : Fin a) (π : CuspSub E a) (ω : HChar E),
    ω.IsUnitary → π.HasCentChar ω → ∀ F : GA E a → ℂ, F ∈ GlobalTheory.JSW.mspanR π →
    ∀ (Φ : (Fin a → Cinf E) → ℂ), ContDiff ℝ (⊤ : ℕ∞) Φ → HasCompactSupport Φ → tsupport Φ ⊆ GlobalTheory.RSTheta.rowSet E ℓ →
    (∀ u, 0 ≤ (Φ u).re ∧ (Φ u).im = 0) →
    ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)),
    IsFundamentalDomain (ratGL E a).range 𝓕 μ → ∀ x : ℝ, 1 < x →
    ∫⁻ g in 𝓕, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖GlobalTheory.RSTheta.rsPsi ℓ F F Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ₑ) * ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) ∂μ ≠ ⊤ := by
  intro E _ _ _ a ℓ π ω hω hc F hF Φ hΦ hcs hs hpos J η μ _ 𝓕 h𝓕 x hx
  have hπ : π.IsUnitary := ⟨ω, hω, CuspSub.hasCentral_iff.2 hc⟩
  obtain ⟨φ, rfl, hw⟩ := GlobalTheory.JSW.mspanR_words GlobalTheory.CuspOrth.cuspFormsBounded hπ F hF
  have hcont : Continuous φ.1 := by simpa [GlobalTheory.JSW.word_nil] using (hw []).2.cont
  have hrsm : φ ∈ GlobalTheory.RSThetaLowM.rsm π := hF
  obtain ⟨hsum, hup, -⟩ := GlobalTheory.RSThetaM.theta_integral_upper_mspan E a ℓ π π hπ hπ φ φ (Or.inr hF) (Or.inr hF) Φ
    hΦ.continuous hcs hs J η μ 𝓕 h𝓕
  have hlow := (GlobalTheory.RSThetaLowM.integral_low_eq J η hπ hπ hrsm hrsm hcont hcont ⟨hΦ, hcs, hs⟩ h𝓕 (s := (x : ℂ))
    (by simpa using hx)).1
  have hpt : ∀ g : GA E a, (∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
      ‖rsPsi ℓ φ.1 φ.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ₑ) *
        ENNReal.ofReal ((ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) =
      ENNReal.ofReal ((∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
        ‖rsPsi ℓ φ.1 φ.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖) *
          (ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) := by
    intro g
    rw [ENNReal.ofReal_mul (tsum_nonneg fun _ => norm_nonneg _),
      ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hsum g)]
    simp only [ofReal_norm_eq_enorm]
  have hlow' : IntegrableOn (fun g : GA E a => (∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
      ‖rsPsi ℓ φ.1 φ.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖) *
        (ideleModule E (GeneralLinearGroup.det g) : ℝ) ^ x) (𝓕 ∩ GlobalTheory.RSThetaLow.lowSet E a) μ := by
    refine hlow.norm.congr (.of_forall fun g => ?_)
    have e : ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, rsPsi ℓ φ.1 φ.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val) =
        (((∑' ξ : {ξ : Fin a → E // ξ ≠ 0},
          ‖rsPsi ℓ φ.1 φ.1 Φ J η g ((fun j => algebraMap E (Ad E) (ξ.1 j)) ᵥ* g.val)‖ : ℝ)) : ℂ) := by
      rw [Complex.ofReal_tsum]
      exact tsum_congr fun ξ => rsPsi_self_eq_norm ℓ φ.1 hpos J η g _
    simp only
    rw [← GlobalTheory.RSThetaLow.tsum_rsPsi_eq_tsum_ne_zero J η _ _ hs g, norm_mul, e, Complex.norm_real,
      Real.norm_of_nonneg (tsum_nonneg fun _ => norm_nonneg _),
      Complex.norm_cpow_eq_rpow_re_of_pos (ideleModule E _).2, Complex.ofReal_re]
  have h1 := (hup x).lintegral_lt_top
  have h2 := hlow'.lintegral_lt_top
  have hsub : 𝓕 ⊆ (𝓕 ∩ {g | 1 ≤ (ideleModule E (GeneralLinearGroup.det g) : ℝ)}) ∪ (𝓕 ∩ GlobalTheory.RSThetaLow.lowSet E a) := by
    intro g hg
    rcases le_total 1 (ideleModule E (GeneralLinearGroup.det g) : ℝ) with h | h
    · exact Or.inl ⟨hg, h⟩
    · exact Or.inr ⟨hg, h⟩
  rw [lintegral_congr hpt]
  exact ne_of_lt ((lintegral_mono_set hsub).trans_lt ((lintegral_union_le _ _ _).trans_lt (ENNReal.add_lt_top.2 ⟨h1, h2⟩)))

end GlobalTheory.RSThetaSelf

end
