import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.StLocB

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.small_pf :
    UpperTheory.Gal.Gen.SymEx → UpperTheory.Gal.Gen.StarEx → UpperTheory.Gal.Gen.NullZero → UpperTheory.Gal.Gen.DensCont → UpperTheory.Gal.Gen.Small := by
  intro hSym hStar hNull hDens n Φ hΦ δ hδ
  obtain ⟨P, hPmem, hPprod, hPpoly⟩ := hSym n Φ
  obtain ⟨Ψ, hΨ, hPΨ⟩ := hPpoly hΦ
  obtain ⟨Q, hQmem, hQ⟩ := hStar n P hPmem
  obtain ⟨-, -, hcont, hnorm⟩ := hDens n 0 le_rfl one_pos
  obtain ⟨M, hM⟩ := (isCompact_univ : IsCompact (Set.univ : Set (Fin n → UnitAddCircle))).exists_bound_of_continuousOn
    (hcont P).continuousOn
  set c : ℝ := 1 / (M ^ 2 + 1) with hc
  have hc0 : 0 < c := by positivity
  let g : (Fin n → UnitAddCircle) → ℝ := fun θ => 1 - c * ‖evalAt (pt θ) P‖ ^ 2
  have hg0 : ∀ θ, 0 ≤ g θ := by
    intro θ
    have h1 : ‖evalAt (pt θ) P‖ ≤ M := hM θ (Set.mem_univ _)
    have h2 : ‖evalAt (pt θ) P‖ ^ 2 ≤ M ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : c * ‖evalAt (pt θ) P‖ ^ 2 ≤ 1 := by
      rw [hc, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
      linarith
    simp only [g]
    linarith
  have hg1 : ∀ θ, g θ ≤ 1 := by
    intro θ
    simp only [g]
    have : 0 ≤ c * ‖evalAt (pt θ) P‖ ^ 2 := by positivity
    linarith
  let pk : ℕ → LaurentRing n := fun k => (1 - (c : ℂ) • (P * Q)) ^ k
  have hpk_mem : ∀ k, pk k ∈ symmetricLaurent n := by
    intro k
    exact Subalgebra.pow_mem _ (Subalgebra.sub_mem _ (Subalgebra.one_mem _)
      (Subalgebra.smul_mem _ (Subalgebra.mul_mem _ hPmem hQmem) _)) k
  have hpk_eval : ∀ k θ, evalAt (pt θ) (pk k) = ((g θ : ℝ) : ℂ) ^ k := by
    intro k θ
    simp only [pk, g, map_pow, map_sub, map_one, map_smul, map_mul, smul_eq_mul]
    rw [hQ (pt θ) (hnorm θ), Complex.mul_conj']
    push_cast
    ring
  have hF : ∀ k θ, ‖evalAt (pt θ) (pk k)‖ ^ 2 = (g θ ^ k) ^ 2 := by
    intro k θ
    rw [hpk_eval, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg0 θ)]
  have hlim : Filter.Tendsto (fun k => ∫ θ, ‖evalAt (pt θ) (pk k)‖ ^ 2) Filter.atTop
      (nhds (∫ _θ : Fin n → UnitAddCircle, (0 : ℝ))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) (fun k => ?_) (integrable_const _)
      (fun k => Filter.Eventually.of_forall (fun θ => ?_)) ?_
    · exact ((hcont (pk k)).norm.pow 2).aestronglyMeasurable
    · rw [hF, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_one₀ (pow_nonneg (hg0 θ) _) (pow_le_one₀ (hg0 θ) (hg1 θ))
    · filter_upwards [hNull n Ψ hΨ] with θ hθ
      have hP0 : evalAt (pt θ) P ≠ 0 := by rw [hPΨ]; exact hθ
      have hlt : g θ < 1 := by
        simp only [g]
        have : 0 < c * ‖evalAt (pt θ) P‖ ^ 2 := by
          have := norm_pos_iff.mpr hP0
          positivity
        linarith
      simp only [hF]
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (hg0 θ) hlt).pow 2
      simpa using h
  rw [MeasureTheory.integral_zero] at hlim
  obtain ⟨k, hk⟩ := ((tendsto_order.1 hlim).2 δ hδ).exists
  refine ⟨pk k, hpk_mem k, fun z hz => ?_, hk.le⟩
  have hP0 : evalAt z P = 0 := by
    rw [hPprod]
    exact Finset.prod_eq_zero (Finset.mem_univ 1) (by simpa using hz)
  simp only [pk, map_pow, map_sub, map_one, map_smul, map_mul, hP0, zero_mul, smul_zero, sub_zero, one_pow]
