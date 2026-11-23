import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.OrbitVanishingLocal
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.WPresGrZeroIsCOOfMemMaximalIdeal
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GrGen

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.isWRing :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O ℤ R) (h : W.HasOrigin), (∀ s, -2 ≤ W.wt s ∧ W.wt s ≤ 2) → IsWRing W.gr (W.originA h) := by
  classical
  intro O _ _ _ _ R _ _ _ W h hw
  haveI := W.fin
  have hz : ∀ s, W.z s ∈ maximalIdeal R := by
    intro s
    by_contra hs
    have hu : IsUnit (W.z s) := by
      by_contra hn
      exact hs ((IsLocalRing.mem_maximalIdeal _).2 hn)
    have h0 : W.origin h (W.z s) = 0 := by
      simp only [WPres.z, WPres.origin_π, MvPowerSeries.constantCoeff_X]
    have hu' := hu.map (W.origin h)
    rw [h0] at hu'
    exact not_isUnit_zero hu'
  refine ⟨wPres_gr_zero_isCO_of_mem_maximalIdeal O ℤ R W hz, ?_, ?_⟩
  · refine ⟨(Finset.univ.filter (fun i => W.wt i ≠ 0)).image W.zA, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hx
      have hi' : W.wt i ≠ 0 := (Finset.mem_filter.1 hi).2
      have hm : W.zA i ∈ W.gr (W.wt i) := W.z_mem i
      obtain ⟨h1, h2⟩ := hw i
      rcases (show W.wt i = -2 ∨ W.wt i = -1 ∨ W.wt i = 1 ∨ W.wt i = 2 by omega) with e | e | e | e
      · exact Or.inl (e ▸ hm)
      · exact Or.inr (Or.inl (e ▸ hm))
      · exact Or.inr (Or.inr (Or.inl (e ▸ hm)))
      · exact Or.inr (Or.inr (Or.inr (e ▸ hm)))
    · refine top_unique ?_
      rw [← gr_gen O R ℤ W]
      apply Algebra.adjoin_mono
      rintro x (hx | ⟨i, rfl⟩)
      · exact Or.inl hx
      · by_cases hi : W.wt i = 0
        · left
          have hm : W.zA i ∈ W.gr (W.wt i) := W.z_mem i
          rw [hi] at hm
          exact hm
        · right
          simp only [Finset.coe_image, Finset.coe_filter, Finset.mem_univ, true_and]
          exact ⟨i, hi, rfl⟩
  · intro j hj f hf
    obtain ⟨g, hg, hgf⟩ := Submodule.mem_map.1 hf
    have hc : MvPowerSeries.constantCoeff g = 0 := by
      have := hg 0 (by simpa using hj.symm)
      simpa [MvPowerSeries.coeff_zero_eq_constantCoeff] using this
    have hfg : (f : R) = W.π g := hgf.symm
    change W.origin h f.1 = 0
    rw [hfg, WPres.origin_π, hc]
