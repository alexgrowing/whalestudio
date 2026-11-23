import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerPureTensorFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerLocalTateIntegral

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.R Ad3.SchwartzSpaceL2
open scoped ValuativeRel ENNReal NNReal

namespace GlobalTheory.CompanionTheory.RSPlane

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

theorem chF_coe (c : Fˣ →* ℂˣ) (s : ℂ) (u : Fˣ) : chF c s (u : F) = ((c u : ℂˣ) : ℂ) * mp u s := by
  simp [chF, u.ne_zero]

theorem measurable_chF {c : Fˣ →* ℂˣ} (hc : Continuous c) (s : ℂ) : Measurable (chF c s) := by
  have hcont : Continuous (fun u : Fˣ => ((c u : ℂˣ) : ℂ) * mp u s) := by
    refine (Units.continuous_val.comp hc).mul ?_
    unfold mp
    refine (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp
      (continuous_modulus.comp Units.continuous_val))).cpow continuous_const fun u => ?_
    exact Complex.ofReal_mem_slitPlane.mpr (by exact_mod_cast modulus_pos u.ne_zero)
  have he : chF c s = Function.extend (Units.val : Fˣ → F)
      (fun u : Fˣ => ((c u : ℂˣ) : ℂ) * mp u s) (fun _ => 0) := by
    funext t
    by_cases h : t = 0
    · subst h
      rw [Function.extend_apply']
      · simp [chF]
      · rintro ⟨u, hu⟩
        exact u.ne_zero hu
    · have := Units.val_injective.extend_apply (fun u : Fˣ => ((c u : ℂˣ) : ℂ) * mp u s)
        (fun _ => (0 : ℂ)) (Units.mk0 t h)
      rw [Units.val_mk0] at this
      rw [this, ← chF_coe, Units.val_mk0]
  rw [he]
  exact measurableEmbedding_units_val.measurable_extend hcont.measurable measurable_const

theorem mp_mul_mp_one (u : Fˣ) (σ : ℂ) : mp u (σ - 1) * mp u 1 = mp u σ := by
  unfold mp
  have h0 : ((modulus (u : F) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (modulus_pos u.ne_zero).ne'
  rw [← Complex.cpow_add _ _ h0, sub_add_cancel]

theorem integrable_mul_chF (ψ : AddChar F Circle) {g : F → ℂ} (hg : g ∈ schwartzBruhat F)
    {c : Fˣ →* ℂˣ} (hc : IsUnit1 c) {σ : ℂ} (hσ : 0 < σ.re) :
    Integrable (fun t => g t * chF c (σ - 1) t) (selfDualMeasure ψ) := by
  set h : F → ℂ := fun t => g t * chF c (σ - 1) t with hh
  have hm : Measurable h := hg.1.continuous.measurable.mul (measurable_chF hc.1 _)
  have hZ := integrable_localZeta hg hc.1 (s := σ)
    (by rw [GlobalTheory.CompanionTheory.TateFE.quasiCharExponent_eq_zero_of_unit hc]; simpa using hσ)
  have hfin := hZ.2
  rw [hasFiniteIntegral_iff_enorm] at hfin
  have hG : Measurable (fun x : F => ‖h x‖ₑ * (modulus x : ℝ≥0∞)) :=
    hm.enorm.mul measurable_modulus.coe_nnreal_ennreal
  have h1 := lintegral_multHaar hG
  have h2 : ∫⁻ u : Fˣ, ‖h u‖ₑ * (modulus (u : F) : ℝ≥0∞) ∂multHaar F =
      ∫⁻ u : Fˣ, ‖g u * ((c u : ℂˣ) : ℂ) * ((modulus (u : F) : ℝ) : ℂ) ^ σ‖ₑ ∂multHaar F := by
    refine lintegral_congr fun u => ?_
    have e : g u * ((c u : ℂˣ) : ℂ) * ((modulus (u : F) : ℝ) : ℂ) ^ σ =
        h u * ((modulus (u : F) : ℝ) : ℂ) := by
      have := mp_mul_mp_one u σ
      simp only [hh, chF_coe]
      have h3 : mp u 1 = ((modulus (u : F) : ℝ) : ℂ) := by simp [mp]
      rw [h3] at this
      have h4 : ((modulus (u : F) : ℝ) : ℂ) ^ σ = mp u σ := rfl
      rw [h4, ← this]
      ring
    have hn : ‖((modulus (u : F) : ℝ) : ℂ)‖ₑ = (modulus (u : F) : ℝ≥0∞) := by
      rw [enorm_eq_nnnorm]
      congr 1
      ext
      simp
    rw [e, enorm_mul (h u), hn]
  have h5 : ∫⁻ x in ({0}ᶜ : Set F), ((modulus x : ℝ≥0∞))⁻¹ * (‖h x‖ₑ * (modulus x : ℝ≥0∞))
      ∂haarIntegers F = ∫⁻ x, ‖h x‖ₑ ∂haarIntegers F := by
    have hae : ∀ᵐ x ∂haarIntegers F, x ∈ ({0}ᶜ : Set F) := by
      rw [ae_iff]
      simpa using haarIntegers_singleton_zero (K := F)
    conv_rhs => rw [← Measure.restrict_eq_self_of_ae_mem hae]
    refine setLIntegral_congr_fun (measurableSet_singleton 0).compl fun x hx => ?_
    have a0 : (modulus x : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr (modulus_ne_zero hx)
    rw [mul_comm (‖h x‖ₑ), ← mul_assoc, ENNReal.inv_mul_cancel a0 ENNReal.coe_ne_top, one_mul]
  rw [h2, h5] at h1
  have h6 : ∫⁻ x, ‖h x‖ₑ ∂haarIntegers F < ∞ := by
    rw [h1] at hfin
    rw [lt_top_iff_ne_top]
    intro this
    rw [this, ENNReal.mul_top multHaarConst_ne_zero] at hfin
    exact lt_irrefl _ hfin
  have h7 : Integrable h (haarIntegers F) :=
    ⟨hm.aestronglyMeasurable, by rw [hasFiniteIntegral_iff_enorm]; exact h6⟩
  unfold selfDualMeasure
  exact h7.smul_measure_nnreal

theorem mul_integral_chF {ψ : AddChar F Circle} {C : ℂ}
    (hC : ∀ G : F → ℂ, ∫ a : Fˣ, G a * mp a 1 ∂multHaar F = C * ∫ t, G t ∂selfDualMeasure ψ)
    (g : F → ℂ) (c : Fˣ →* ℂˣ) (σ : ℂ) :
    C * ∫ t, g t * chF c (σ - 1) t ∂selfDualMeasure ψ = localZeta g c σ := by
  rw [← hC]
  unfold localZeta
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  have h4 : ((modulus (u : F) : ℝ) : ℂ) ^ σ = mp u σ := rfl
  simp only [chF_coe, h4, ← mp_mul_mp_one u σ]
  ring

theorem key_one {ψ : AddChar F Circle} (hψ : IsStd ψ) {C : ℂ} (hC0 : C ≠ 0)
    (hC : ∀ G : F → ℂ, ∫ a : Fˣ, G a * mp a 1 ∂multHaar F = C * ∫ t, G t ∂selfDualMeasure ψ)
    {χ : Fˣ →* ℂˣ} (hχ : IsUnit1 χ) {g : F → ℂ} (hg : g ∈ schwartzBruhat F) {s : ℂ} (hs : Strip s) :
    ∫ t, localFourier (selfDualMeasure ψ) ψ g t * chF χ⁻¹ (-s) t ∂selfDualMeasure ψ =
      gam ψ χ s * ∫ t, g t * chF χ (s - 1) t ∂selfDualMeasure ψ := by
  have h1 := mul_integral_chF hC (localFourier (selfDualMeasure ψ) ψ g) χ⁻¹ (1 - s)
  have h2 := mul_integral_chF hC g χ s
  have h3 := GlobalTheory.CompanionTheory.TateFE.first_form hψ hχ hg hs.1 hs.2
  have e : (1 - s - 1 : ℂ) = -s := by ring
  rw [e] at h1
  apply mul_left_cancel₀ hC0
  rw [h1, h3, ← h2]
  ring

theorem integral_plane_measure_product (ψ : AddChar F Circle) (a b : F → ℂ) :
    ∫ r, a (r 0) * b (r 1) ∂m2 ψ =
      (∫ t, a t ∂selfDualMeasure ψ) * ∫ t, b t ∂selfDualMeasure ψ := by
  have := integral_fintype_prod_eq_prod (𝕜 := ℂ) (ι := Fin 2) (E := fun _ => F)
    (μ := fun _ => selfDualMeasure ψ) (fun i => ![a, b] i)
  simpa [Fin.prod_univ_two, m2] using this

theorem integrable_plane_measure_product (ψ : AddChar F Circle) {a b : F → ℂ}
    (ha : Integrable a (selfDualMeasure ψ)) (hb : Integrable b (selfDualMeasure ψ)) :
    Integrable (fun r : Fin 2 → F => a (r 0) * b (r 1)) (m2 ψ) := by
  have := Integrable.fintype_prod (𝕜 := ℂ) (ι := Fin 2) (E := F)
    (μ := fun _ => selfDualMeasure ψ) (f := fun i => ![a, b] i)
    (fun i => by fin_cases i <;> simpa)
  simpa [Fin.prod_univ_two, m2] using this

theorem integral_plane_measure_sum_products (ψ : AddChar F Circle) {n : ℕ} {A B : Fin n → F → ℂ}
    (hA : ∀ i, Integrable (A i) (selfDualMeasure ψ)) (hB : ∀ i, Integrable (B i) (selfDualMeasure ψ)) :
    ∫ r, ∑ i, A i (r 0) * B i (r 1) ∂m2 ψ =
      ∑ i, (∫ t, A i t ∂selfDualMeasure ψ) * ∫ t, B i t ∂selfDualMeasure ψ := by
  rw [integral_finset_sum _ fun i _ => integrable_plane_measure_product ψ (hA i) (hB i)]
  exact Finset.sum_congr rfl fun i _ => integral_plane_measure_product ψ _ _

theorem integrable_mul_char {ψ : AddChar F Circle} (hψ : Continuous ψ) {g : F → ℂ}
    (hg : g ∈ schwartzBruhat F) (y : F) :
    Integrable (fun x => g x * (ψ (x * y) : ℂ)) (selfDualMeasure ψ) := by
  refine Continuous.integrable_of_hasCompactSupport
    (hg.1.continuous.mul ?_) hg.2.mul_right
  exact continuous_induced_dom.comp (hψ.comp (continuous_id.mul continuous_const))

theorem plane_fourier_sum {ψ : AddChar F Circle} (hψ : Continuous ψ) {n : ℕ} {a b : Fin n → F → ℂ}
    (ha : ∀ i, a i ∈ schwartzBruhat F) (hb : ∀ i, b i ∈ schwartzBruhat F) (r : Fin 2 → F) :
    ∫ r', (∑ i, SchwartzSpaceL2.pt (a i) (b i)) r' * (ψ (r' 0 * r 0 + r' 1 * r 1) : ℂ) ∂m2 ψ =
      ∑ i, localFourier (selfDualMeasure ψ) ψ (a i) (r 0) *
        localFourier (selfDualMeasure ψ) ψ (b i) (r 1) := by
  have e : ∀ r' : Fin 2 → F, (∑ i, SchwartzSpaceL2.pt (a i) (b i)) r' * (ψ (r' 0 * r 0 + r' 1 * r 1) : ℂ) =
      ∑ i, (fun x => a i x * (ψ (x * r 0) : ℂ)) (r' 0) * (fun x => b i x * (ψ (x * r 1) : ℂ)) (r' 1) := by
    intro r'
    rw [Finset.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [SchwartzSpaceL2.pt, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  simp_rw [e]
  rw [integral_plane_measure_sum_products ψ (fun i => integrable_mul_char hψ (ha i) _)
    (fun i => integrable_mul_char hψ (hb i) _)]
  rfl

theorem a7 : Ad3.R.A2 → Ad3.R.A7 := by
  intro hA2 F _ _ _ _ _ _ ψ hψ χ₁ χ₂ h₁ h₂ f hf s hs
  obtain ⟨C, hC0, hC, -⟩ := hA2 F ψ hψ
  obtain ⟨n, a, b, hab, rfl⟩ := GlobalTheory.CompanionTheory.PlanePure.schwartzBruhat2_eq_sum_pt F f hf
  have ha : ∀ i, a i ∈ schwartzBruhat F := fun i => (hab i).1
  have hb : ∀ i, b i ∈ schwartzBruhat F := fun i => (hab i).2
  have hs' : 0 < (1 - s).re := by
    have := hs.2
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  have e1 : (1 - s - 1 : ℂ) = -s := by ring
  have hT : ∀ {g : F → ℂ}, g ∈ schwartzBruhat F →
      localFourier (selfDualMeasure ψ) ψ g ∈ schwartzBruhat F := fun hg =>
    localFourier_mem_schwartzBruhat (selfDualMeasure ψ) hψ.1 hψ.2.1 hg
  have hI : ∀ {g : F → ℂ} {χ : Fˣ →* ℂˣ}, g ∈ schwartzBruhat F → IsUnit1 χ →
      Integrable (fun t => localFourier (selfDualMeasure ψ) ψ g t * chF χ⁻¹ (-s) t)
        (selfDualMeasure ψ) := by
    intro g χ hg hχ
    have hχ' : IsUnit1 χ⁻¹ := ⟨continuous_quasiChar_inv hχ.1, fun x => by
      simp [hχ.2]⟩
    have := integrable_mul_chF ψ (hT hg) hχ' hs'
    rwa [e1] at this
  have hL : ∫ r, (∫ r', (∑ i, SchwartzSpaceL2.pt (a i) (b i)) r' * (ψ (r' 0 * r 0 + r' 1 * r 1) : ℂ) ∂m2 ψ) *
      (chF χ₁⁻¹ (-s) (r 0) * chF χ₂⁻¹ (-s) (r 1)) ∂m2 ψ =
      ∑ i, (∫ t, localFourier (selfDualMeasure ψ) ψ (a i) t * chF χ₁⁻¹ (-s) t ∂selfDualMeasure ψ) *
        ∫ t, localFourier (selfDualMeasure ψ) ψ (b i) t * chF χ₂⁻¹ (-s) t ∂selfDualMeasure ψ := by
    rw [← integral_plane_measure_sum_products ψ (fun i => hI (ha i) h₁) (fun i => hI (hb i) h₂)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    simp only []
    rw [plane_fourier_sum hψ.1 ha hb r, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hR : ∫ r, (∑ i, SchwartzSpaceL2.pt (a i) (b i)) r * (chF χ₁ (s - 1) (r 0) * chF χ₂ (s - 1) (r 1)) ∂m2 ψ =
      ∑ i, (∫ t, a i t * chF χ₁ (s - 1) t ∂selfDualMeasure ψ) *
        ∫ t, b i t * chF χ₂ (s - 1) t ∂selfDualMeasure ψ := by
    rw [← integral_plane_measure_sum_products ψ (fun i => integrable_mul_chF ψ (ha i) h₁ hs.1)
      (fun i => integrable_mul_chF ψ (hb i) h₂ hs.1)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    simp only []
    rw [Finset.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [SchwartzSpaceL2.pt]
    ring
  rw [hL, hR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [key_one hψ hC0 hC h₁ (ha i) hs, key_one hψ hC0 hC h₂ (hb i) hs]
  ring

end GlobalTheory.CompanionTheory.RSPlane

end
