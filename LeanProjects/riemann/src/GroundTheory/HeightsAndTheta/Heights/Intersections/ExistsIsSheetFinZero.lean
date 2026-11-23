import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGood
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherLast
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory Filter

noncomputable section

theorem maDensity_fin_zero (φ : Fin 0 → (Fin 0 → ℂ) → ℝ) (y : Fin 0 → ℂ) : maDensity φ y = 1 := by
  simp [maDensity, mixedDisc]

theorem exists_isSheet_fin_zero {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ)}
    {y : Fin 0 → ℂ} {w : ((k : K) → ι k) → ℂ} (hw : w ∈ fibre P Ψ y) : ∃ γ, IsSheet P Ψ y w γ := by
  obtain ⟨z, hz, rfl, hΨ⟩ := hw
  refine ⟨fun _ => z, rfl, Eventually.of_forall fun y' => ⟨differentiableAt_const _, hz, ?_⟩⟩
  rw [Subsingleton.elim y' y]
  exact hΨ

theorem regularityPointsSum_holds.proof : regularityPointsSum_holds.Statement := by
  classical
  intro K _ ι _ P hP
  obtain ⟨k₀⟩ := hP.1
  have hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (0 + 1) → ℂ), IsGoodProj P Ψ :=
    goodProjExists K ι P 0 hP
  have hgood : IsGoodProj P hΨ.choose := hΨ.choose_spec
  have hF : (fibre P hΨ.choose (default : Fin 0 → ℂ)).Finite :=
    fibreFinite K ι P 0 hΨ.choose hP hgood default
  let pick : (((k : K) → ι k) → ℂ) → (Σ k, ι k) → ℂ := fun w =>
    if hγ : ∃ γ, IsSheet P hΨ.choose default w γ then hγ.choose default else 0
  have hpick : ∀ w ∈ fibre P hΨ.choose default, pick w ∈ mcPts P ∧ segre (pick w) = w := by
    intro w hw
    have hγ := exists_isSheet_fin_zero hw
    simp only [pick, dif_pos hγ]
    exact ⟨hγ.choose_spec.2.self_of_nhds.2.1, hγ.choose_spec.1⟩
  have hone : ∀ w ∈ fibre P hΨ.choose default, hΨ.choose w 0 = 1 := by
    rintro w ⟨_, _, _, h⟩
    rw [h]
    rfl
  have hR : ∀ t ∈ hF.toFinset.image pick, ∃ w ∈ fibre P hΨ.choose default, t = pick w := by
    intro t ht
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp ht
    exact ⟨w, hF.mem_toFinset.mp hw, rfl⟩
  refine ⟨hF.toFinset.image pick, fun t ht => ?_, fun z hz => ?_, fun h _ => ?_⟩
  · obtain ⟨w, hw, rfl⟩ := hR t ht
    exact (hpick w hw).1
  · have ha : hΨ.choose (segre z) 0 ≠ 0 := fun h0 =>
      hgood z hz (funext fun i => by rw [Fin.eq_zero i]; exact h0)
    set a := hΨ.choose (segre z) 0 with ha_def

    let c : K → ℂ := fun k => if k = k₀ then a⁻¹ else 1
    have hc : ∀ k, c k ≠ 0 := fun k => by by_cases h : k = k₀ <;> simp [c, h, ha]
    have hprod : ∏ k, c k = a⁻¹ := by
      rw [Finset.prod_eq_single k₀ (fun k _ hk => by simp [c, hk]) (by simp)]
      simp [c]
    have hw₁ : segre (fun p => c p.1 * z p) ∈ fibre P hΨ.choose default := by
      refine ⟨_, mcPts_smul hP.2.1.2.1 c hc hz, rfl, funext fun i => ?_⟩
      rw [Fin.eq_zero i, segre_smul, hprod, map_smul, Pi.smul_apply, smul_eq_mul,
        ← ha_def, inv_mul_cancel₀ ha]
      rfl
    have hseg₁ : segre (fun p => c p.1 * z p) = a⁻¹ • segre z := by rw [segre_smul, hprod]

    have horb : ∀ t ∈ hF.toFinset.image pick, SameOrbit z t → segre t = a⁻¹ • segre z := by
      intro t ht ⟨c', _, hzt⟩
      obtain ⟨w, hw, rfl⟩ := hR t ht
      have hs : segre z = (∏ k, c' k) • segre (pick w) := by rw [hzt, segre_smul]
      have h1 : a = ∏ k, c' k := by
        rw [ha_def, hs, map_smul, Pi.smul_apply, smul_eq_mul, (hpick w hw).2, hone w hw, mul_one]
      rw [hs, ← h1, smul_smul, inv_mul_cancel₀ ha, one_smul]
    refine ⟨pick (segre (fun p => c p.1 * z p)), ⟨Finset.mem_image_of_mem _ (hF.mem_toFinset.mpr hw₁), ?_⟩,
      fun t ⟨ht, hzt⟩ => ?_⟩
    · refine sameOrbit_of_segre (hpick _ hw₁).1.1 a ha ?_
      rw [(hpick _ hw₁).2, hseg₁, smul_smul, mul_inv_cancel₀ ha, one_smul]
    · obtain ⟨w, hw, rfl⟩ := hR t ht
      have hw' : w = segre (fun p => c p.1 * z p) := by
        rw [← (hpick w hw).2, horb _ ht hzt, hseg₁]
      rw [hw']
  · unfold ptsIntegral
    rw [dif_pos hΨ]
    unfold ptsIntegralAt
    rw [integral_unique]
    have hvol : (volume : Measure (Fin 0 → ℂ)).real Set.univ = 1 := by
      simp [Measure.real, MeasureTheory.volume_pi]
    rw [hvol, one_smul]
    refine (?_ : ∀ y : Fin 0 → ℂ, ∑ᶠ w ∈ fibre P hΨ.choose y,
      sheetDensity P hΨ.choose (Fin.elim0 : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) h y w =
        ∑ t ∈ hF.toFinset.image pick, h t) _
    intro y
    rw [Subsingleton.elim y default, finsum_mem_eq_finite_toFinset_sum _ hF,
      Finset.sum_image fun x hx y hy hxy => by
        rw [← (hpick x (hF.mem_toFinset.mp hx)).2, hxy, (hpick y (hF.mem_toFinset.mp hy)).2]]
    refine Finset.sum_congr rfl fun w hw => ?_
    have hγ := exists_isSheet_fin_zero (hF.mem_toFinset.mp hw)
    unfold sheetDensity
    rw [dif_pos hγ, maDensity_fin_zero, mul_one]
    simp only [pick, dif_pos hγ]

end

end GroundTheory.Heights₂.Heights.Inter
