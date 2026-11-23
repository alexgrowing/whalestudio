import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LintegralLintegralNormSqRiemannTheta

open MeasureTheory Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.ThetaMean

theorem mean_image {ι κ : Type} [Fintype ι] [Fintype κ] (L : (ι → ℝ) ≃L[ℝ] (κ → ℂ))
    {s : Set (ι → ℝ)} (hs : volume s = 1) (f : (κ → ℂ) → ℝ) :
    (∫ z in L '' s, f z) / (volume (L '' s)).toReal = ∫ p in s, f (L p) := by
  have hL : MeasurableEmbedding L := L.toHomeomorph.measurableEmbedding
  have : (Measure.map L (volume : Measure (ι → ℝ))).IsAddHaarMeasure := L.isAddHaarMeasure_map _
  set c := Measure.addHaarScalarFactor (volume : Measure (κ → ℂ)) (Measure.map L volume) with hc_def
  have hc : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  have hvol : (volume : Measure (κ → ℂ)) = c • Measure.map L volume :=
    Measure.isAddLeftInvariant_eq_smul _ _
  have hpre : L ⁻¹' (L '' s) = s := Set.preimage_image_eq s L.injective
  have h1 : (volume (L '' s)).toReal = c := by
    rw [hvol, Measure.smul_apply, hL.map_apply, hpre, hs]
    simp
  have h2 : ∫ z in L '' s, f z = c * ∫ p in s, f (L p) := by
    rw [hvol, Measure.restrict_smul, integral_smul_nnreal_measure, hL.restrict_map, hpre,
      hL.integral_map, NNReal.smul_def, smul_eq_mul]
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  rw [h2, h1, mul_div_cancel_left₀ _ hc']

def periodMap {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) : (Fin g ⊕ Fin g → ℝ) →ₗ[ℝ] (Fin g → ℂ) where
  toFun p := (fun i => (p (.inl i) : ℂ)) + τ *ᵥ (fun i => (p (.inr i) : ℂ))
  map_add' p q := by
    funext i
    simp [mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' r p := by
    funext i
    simp [mulVec, dotProduct, mul_add, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

theorem periodMap_apply {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (p : Fin g ⊕ Fin g → ℝ) :
    periodMap τ p = (fun i => (p (.inl i) : ℂ)) + τ *ᵥ (fun i => (p (.inr i) : ℂ)) := rfl

theorem im_periodMap {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (p : Fin g ⊕ Fin g → ℝ) :
    (fun i => (periodMap τ p i).im) = τ.map Complex.im *ᵥ fun i => p (.inr i) := by
  funext i
  simp [periodMap_apply, mulVec, dotProduct, Complex.im_sum]

theorem periodMap_bijective {g : ℕ} {τ : Matrix (Fin g) (Fin g) ℂ}
    (hp : (τ.map Complex.im).PosDef) : Function.Bijective (periodMap τ) := by
  have hinj : Function.Injective (periodMap τ) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp0
    have him := im_periodMap τ p
    rw [hp0] at him
    have h2 : (fun i => p (.inr i)) = 0 := by
      refine Matrix.eq_zero_of_mulVec_eq_zero hp.det_pos.ne' ?_
      rw [← him]
      rfl
    have h1 : (fun i => (p (.inl i) : ℂ)) = 0 := by
      have := hp0
      rw [periodMap_apply] at this
      have h2' : (fun i => (p (.inr i) : ℂ)) = 0 := by
        funext i
        simp [show p (.inr i) = 0 from congrFun h2 i]
      rw [h2', mulVec_zero, add_zero] at this
      exact this
    funext x
    rcases x with i | i
    · simpa using congrFun h1 i
    · exact congrFun h2 i
  have hrank : Module.finrank ℝ (Fin g ⊕ Fin g → ℝ) = Module.finrank ℝ (Fin g → ℂ) := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex]
    ring
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mp hinj⟩

theorem exists_fundamentalDomain_mean_norm_sq_thetaChar :
    ∀ (g : ℕ) (τ h : Matrix (Fin g) (Fin g) ℂ) (c₁ c₂ : Fin g → ℂ)
      (Λ : AddSubgroup (Fin g → ℂ)), τ.IsSymm → (τ.map Complex.im).PosDef → IsUnit h.det →
      (∀ i, c₁ i = 0 ∨ c₁ i = 1 / 2) → (∀ i, c₂ i = 0 ∨ c₂ i = 1 / 2) →
      (∀ lam, lam ∈ Λ ↔ ∃ m n : Fin g → ℤ,
        h *ᵥ lam = (fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ))) →
      ∃ Fd : Set (Fin g → ℂ), MeasureTheory.IsAddFundamentalDomain Λ Fd MeasureTheory.volume ∧
        (∫ z in Fd, ‖thetaChar τ c₁ c₂ (h *ᵥ z)‖ ^ 2 * Real.exp (-2 * Real.pi *
          ((fun i => ((h *ᵥ z) i).im) ⬝ᵥ (((τ.map Complex.im)⁻¹) *ᵥ fun i => ((h *ᵥ z) i).im)))) /
          (MeasureTheory.volume Fd).toReal =
          (Real.sqrt (2 ^ g * (τ.map Complex.im).det))⁻¹ := by
  intro g τ h c₁ c₂ Λ hsym hY hh hc₁ hc₂ hΛ
  obtain ⟨a, rfl⟩ : ∃ a : Fin g → ℝ, (fun i => (a i : ℂ)) = c₁ := by
    refine ⟨fun i => (c₁ i).re, funext fun i => ?_⟩
    show ((c₁ i).re : ℂ) = c₁ i
    rcases hc₁ i with e | e <;> rw [e] <;> norm_num
  obtain ⟨b, rfl⟩ : ∃ b : Fin g → ℝ, (fun i => (b i : ℂ)) = c₂ := by
    refine ⟨fun i => (c₂ i).re, funext fun i => ?_⟩
    show ((c₂ i).re : ℂ) = c₂ i
    rcases hc₂ i with e | e <;> rw [e] <;> norm_num
  have hcancel : ∀ x : Fin g → ℂ, h⁻¹ *ᵥ (h *ᵥ x) = x := by
    intro x
    rw [mulVec_mulVec, nonsing_inv_mul _ hh, one_mulVec]
  let Pe : (Fin g ⊕ Fin g → ℝ) ≃ₗ[ℝ] (Fin g → ℂ) :=
    LinearEquiv.ofBijective (periodMap τ) (periodMap_bijective hY)
  let Hinv : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) :=
    LinearEquiv.ofLinearMap (Matrix.toLin' h⁻¹) (Matrix.toLin' h)
      (by rw [← Matrix.toLin'_mul, nonsing_inv_mul _ hh, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, mul_nonsing_inv _ hh, Matrix.toLin'_one])
  let Φ : (Fin g ⊕ Fin g → ℝ) ≃L[ℝ] (Fin g → ℂ) :=
    (Pe.trans (Hinv.restrictScalars ℝ)).toContinuousLinearEquiv
  have F1 : ∀ p, h *ᵥ Φ p = periodMap τ p := by
    intro p
    show h *ᵥ (h⁻¹ *ᵥ periodMap τ p) = _
    rw [mulVec_mulVec, mul_nonsing_inv _ hh, one_mulVec]
  let B : Module.Basis (Fin g ⊕ Fin g) ℝ (Fin g → ℂ) :=
    (Pi.basisFun ℝ (Fin g ⊕ Fin g)).map Φ.toLinearEquiv
  have hrepr : ∀ z i, B.repr z i = Φ.symm z i := by
    intro z i
    simp [B]
  have hΛeq : Λ = (Submodule.span ℤ (Set.range B)).toAddSubgroup := by
    ext lam
    rw [hΛ lam, Submodule.mem_toAddSubgroup, Module.Basis.mem_span_iff_repr_mem]
    simp only [hrepr, Set.mem_range, algebraMap_int_eq, eq_intCast]
    constructor
    · rintro ⟨m, n, hmn⟩ i
      have hPq : periodMap τ (Sum.elim (fun i => (m i : ℝ)) (fun i => (n i : ℝ))) =
          (fun i => (m i : ℂ)) + τ *ᵥ (fun i => (n i : ℂ)) := by
        rw [periodMap_apply]
        simp
      have hΦq : Φ (Sum.elim (fun i => (m i : ℝ)) (fun i => (n i : ℝ))) = lam := by
        have e : h *ᵥ Φ (Sum.elim (fun i => (m i : ℝ)) (fun i => (n i : ℝ))) = h *ᵥ lam := by
          rw [F1, hPq, hmn]
        rw [← hcancel (Φ _), e, hcancel]
      rw [← hΦq, Φ.symm_apply_apply]
      rcases i with i | i
      · exact ⟨m i, by simp⟩
      · exact ⟨n i, by simp⟩
    · intro hk
      choose k hk using hk
      refine ⟨fun i => k (.inl i), fun i => k (.inr i), ?_⟩
      rw [← Φ.apply_symm_apply lam, F1, periodMap_apply]
      simp_rw [← hk, Complex.ofReal_intCast]
  have hFd : ZSpan.fundamentalDomain B = Φ '' Set.univ.pi (fun _ => Set.Ico (0 : ℝ) 1) := by
    rw [ContinuousLinearEquiv.image_eq_preimage_symm]
    ext z
    simp [ZSpan.mem_fundamentalDomain, hrepr]
  have hcube : volume (Set.univ.pi fun _ : Fin g ⊕ Fin g => Set.Ico (0 : ℝ) 1) = 1 := by
    simpa using Real.volume_pi_Ico (a := fun _ : Fin g ⊕ Fin g => (0 : ℝ)) (b := fun _ => 1)
  have hYu : IsUnit (τ.map Complex.im).det := hY.det_pos.ne'.isUnit
  refine ⟨ZSpan.fundamentalDomain B, by rw [hΛeq]; exact ZSpan.isAddFundamentalDomain' B _, ?_⟩
  rw [hFd, mean_image Φ hcube, ← GlobalTheory.ThetaNorm.integral_norm_sq_thetaChar g τ a b hsym hY]
  congr 1
  funext p
  rw [F1, im_periodMap, mulVec_mulVec, nonsing_inv_mul _ hYu, one_mulVec, dotProduct_comm,
    periodMap_apply]

end GlobalTheory.ThetaMean
