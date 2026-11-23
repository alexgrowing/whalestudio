import Development.WeilBound.RepresentationTheoryGL.LimitMultiplicityWeights.RegularClassIntegrals.ClosedGraph

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary GlobalTheory.Orb Matrix
open scoped ContDiff ComplexConjugate

noncomputable section

namespace MainStatements.WeightKernel.PIdentOne

def gR {H : Type} [Group H] [TopologicalSpace H] {n : ℕ} (ι : H →* Matrix (Fin n) (Fin n) ℂ) (s : H)
    (B : Mx n × Mx n → ℝ) (φ : H → ℝ) (z h : H) : ℝ :=
  B (matCoord ι (z⁻¹ * s * z), matCoord ι (z⁻¹ * h)) * φ (h⁻¹ * s * h)

def G {H : Type} [Group H] [TopologicalSpace H] {n : ℕ} (ι : H →* Matrix (Fin n) (Fin n) ℂ) (s : H)
    (B : Mx n × Mx n → ℝ) (φ : H → ℝ) (z h : H) : ℂ :=
  (gR ι s B φ z h : ℂ)

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [T2Space H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H] {n : ℕ} {ι : H →* Matrix (Fin n) (Fin n) ℂ}
    {s : H} {B : Mx n × Mx n → ℝ} {φ : H → ℝ}

theorem gR_cont (hι : Continuous (matCoord ι)) (hB : IsWeight ι s B) (hφc : Continuous φ) (z : H) :
    Continuous (gR ι s B φ z) := by
  unfold gR
  have hBc : Continuous B := hB.smooth.continuous
  exact (hBc.comp (continuous_const.prodMk (hι.comp (continuous_const.mul continuous_id)))).mul
    (hφc.comp ((continuous_inv.mul continuous_const).mul continuous_id))

theorem gR_supp (hB : IsWeight ι s B) (hφ : HasCompactSupport φ) (z : H) :
    HasCompactSupport (gR ι s B φ z) := by
  obtain ⟨K, hK, hKp⟩ := hB.proper {z⁻¹ * s * z} (tsupport φ) isCompact_singleton hφ
  refine HasCompactSupport.intro (hK.image (continuous_const_mul z)) fun h hh => ?_
  by_contra hne
  apply hh
  refine ⟨z⁻¹ * h, hKp z (z⁻¹ * h) (Set.mem_singleton _) ?_ ?_, mul_inv_cancel_left z h⟩
  · rw [mul_inv_cancel_left z h]
    exact subset_tsupport _ (fun h0 => hne (by simp [gR, h0]))
  · exact fun h0 => hne (by simp [gR, h0])

theorem fiber (hB : IsWeight ι s B) (dt : Measure (cent s)) [dt.IsMulRightInvariant] (z h : H) :
    ∫ t : cent s, G ι s B φ z (t * h) ∂dt = ∫ t : cent s, G ι s B φ 1 (t * h) ∂dt := by
  obtain ⟨t₀, ht₀, e⟩ := hB.shift z h 1 h
  have key : ∀ v : H, v * s = s * v → (v * h)⁻¹ * s * (v * h) = h⁻¹ * s * h := fun v hv => by
    calc (v * h)⁻¹ * s * (v * h) = h⁻¹ * (v⁻¹ * (s * v)) * h := by group
      _ = h⁻¹ * (v⁻¹ * (v * s)) * h := by rw [hv]
      _ = h⁻¹ * s * h := by group
  have hc : ∀ u : cent s, ((u : H) * h)⁻¹ * s * (u * h) = h⁻¹ * s * h := fun u => key u (mem_cent.1 u.2)
  calc ∫ t : cent s, G ι s B φ z (t * h) ∂dt
        = ∫ t : cent s, G ι s B φ 1 (((t * ⟨t₀, ht₀⟩ : cent s) : H) * h) ∂dt := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
          simp only [G, gR]
          rw [hc t, hc (t * ⟨t₀, ht₀⟩), ← mul_assoc z⁻¹, e t t.2]
          simp [mul_assoc]
    _ = _ := integral_mul_right_eq_self (fun t : cent s => G ι s B φ 1 ((t : H) * h)) ⟨t₀, ht₀⟩

theorem integral_eq (hι : Continuous (matCoord ι)) (hB : IsWeight ι s B) (μ : Measure H) [μ.IsHaarMeasure]
    (dt : Measure (cent s)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant] (hφc : Continuous φ)
    (hφ : HasCompactSupport φ) (z : H) :
    ∫ h, G ι s B φ z h ∂μ = ∫ h, G ι s B φ 1 h ∂μ := by
  have hi : ∀ w, Integrable (G ι s B φ w) μ := fun w =>
    (Complex.continuous_ofReal.comp (gR_cont hι hB hφc w)).integrable_of_hasCompactSupport
      ((gR_supp hB hφ w).comp_left Complex.ofReal_zero)
  have w1 := (weil_integral (dt := dt) (isClosed_cent s) (hi z)).2.2
  have w2 := (weil_integral (dt := dt) (isClosed_cent s) (hi 1)).2.2
  rw [← w1, ← w2]
  exact congrArg (quotInt _ dt μ) (funext fun x => fiber hB dt z x)

theorem orig_eq (μ : Measure H) [μ.IsHaarMeasure] (z : H) :
    ∫ k, (B (matCoord ι (z⁻¹ * s * z), matCoord ι k) : ℂ) * (φ (k⁻¹ * (z⁻¹ * s * z) * k) : ℂ) ∂μ =
      ∫ h, G ι s B φ z h ∂μ := by
  refine (integral_mul_left_eq_self (μ := μ) (fun k => (B (matCoord ι (z⁻¹ * s * z), matCoord ι k) : ℂ) *
    (φ (k⁻¹ * (z⁻¹ * s * z) * k) : ℂ)) z⁻¹).symm.trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
  simp only [G, gR, Complex.ofReal_mul]
  rw [show (z⁻¹ * h)⁻¹ * (z⁻¹ * s * z) * (z⁻¹ * h) = h⁻¹ * s * h by group]

theorem ne_zero (hι : Continuous (matCoord ι)) (hB : IsWeight ι s B) (μ : Measure H) [μ.IsHaarMeasure]
    (hφc : Continuous φ) (hφ : HasCompactSupport φ) (hφ0 : ∀ y, 0 ≤ φ y) (hφs : 0 < φ s) :
    ∫ h, G ι s B φ 1 h ∂μ ≠ 0 := by
  have hpos : 0 < ∫ h, gR ι s B φ 1 h ∂μ := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) (gR_cont hι hB hφc 1)
      (gR_supp hB hφ 1) (fun h => mul_nonneg (hB.nonneg _) (hφ0 _)) ?_
    simp only [gR, inv_one, one_mul, mul_one]
    exact (mul_pos hB.pos hφs).ne'
  simp only [G]
  rw [integral_complex_ofReal]
  exact_mod_cast hpos.ne'

end MainStatements.WeightKernel.PIdentOne

theorem MainStatements.WeightKernel.identOne : IdentOne := by
  intro H _ _ _ _ _ _ _ _ n ι hι s B hB μ _ dt _ _ φ hφc hφ hφ0 hφs
  exact ⟨_, PIdentOne.ne_zero hι hB μ hφc hφ hφ0 hφs, fun z =>
    (PIdentOne.orig_eq μ z).trans (PIdentOne.integral_eq hι hB μ dt hφc hφ z)⟩

end
