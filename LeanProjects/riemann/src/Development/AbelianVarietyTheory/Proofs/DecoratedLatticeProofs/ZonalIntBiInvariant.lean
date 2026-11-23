import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.ZonalBi

theorem zonalInt_biInvariant : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) [μK.IsHaarMeasure], μK (KO k (Fin N)) = 1 → ∀ ψ : GL (Fin N) k → ℂ, (∀ g, ∀ x ∈ KO k (Fin N), ψ (g * x) = ψ g) → ∀ κ ∈ KO k (Fin N), ∀ m, zonalInt μK ψ (κ * m) = zonalInt μK ψ m ∧ zonalInt μK ψ (m * κ) = zonalInt μK ψ m := by
  intro k _ _ _ _ N _ _ μK _ hK ψ hψ κ₀ hκ₀ m
  have hKo : IsOpen (KO k (Fin N) : Set (GL (Fin N) k)) := GlobalTheory.SplitFlip.isOpen_KO
  have hKc : IsCompact (KO k (Fin N) : Set (GL (Fin N) k)) := GlobalTheory.SplitFlip.isCompact_KO
  have hKcl : IsClosed (KO k (Fin N) : Set (GL (Fin N) k)) := Subgroup.isClosed_of_isOpen _ hKo
  have hKfr : frontier (KO k (Fin N) : Set (GL (Fin N) k)) = ∅ := (IsClopen.frontier_eq ⟨hKcl, hKo⟩)
  have hKm : MeasurableSet (KO k (Fin N) : Set (GL (Fin N) k)) := hKo.measurableSet
  have hψc : Continuous ψ := by
    refine continuous_iff_continuousAt.2 fun g => ?_
    have hmem : (fun y => g⁻¹ * y) ⁻¹' (KO k (Fin N) : Set (GL (Fin N) k)) ∈ nhds g :=
      (hKo.preimage (continuous_const_mul g⁻¹)).mem_nhds (by simp [one_mem])
    have hev : ∀ᶠ y in nhds g, ψ y = ψ g := by
      filter_upwards [hmem] with y hy
      have := hψ g (g⁻¹ * y) hy
      rwa [mul_inv_cancel_left] at this
    exact tendsto_nhds_of_eventually_eq hev
  refine ⟨?_, ?_⟩
  · set ν : Measure (GL (Fin N) k) := Measure.map (· * κ₀) μK with hν
    set c := Measure.haarScalarFactor ν μK with hc
    have L : ∀ f : GL (Fin N) k → ℝ, Continuous f → HasCompactSupport f →
        ∫ x, f x ∂ν = ∫ x, f x ∂(c • μK) := fun f hf hs =>
      Measure.integral_isMulLeftInvariant_eq_smul_of_hasCompactSupport ν μK hf hs
    have hpre : (· * κ₀) ⁻¹' (KO k (Fin N) : Set (GL (Fin N) k)) = KO k (Fin N) := by
      ext x; simp [Subgroup.mul_mem_cancel_right _ hκ₀]
    have hc1 : c = 1 := by
      have h1 := L ((KO k (Fin N) : Set (GL (Fin N) k)).indicator 1)
        (continuous_indicator (by simp [hKfr]) continuous_one.continuousOn)
        (HasCompactSupport.intro hKc fun x hx => by simp [hx])
      rw [integral_indicator_one hKm, integral_indicator_one hKm] at h1
      simp only [Measure.real, hν, Measure.map_apply (measurable_mul_const κ₀) hKm, hpre, Measure.smul_apply, hK] at h1
      simpa using h1.symm
    set F : GL (Fin N) k → ℂ := (KO k (Fin N) : Set (GL (Fin N) k)).indicator fun x => ψ (x * m) with hFdef
    have hF : Continuous F :=
      continuous_indicator (by simp [hKfr]) (hψc.comp (continuous_mul_const m)).continuousOn
    have hFs : HasCompactSupport F := HasCompactSupport.intro hKc fun x hx => by simp [F, hx]
    have e1 : zonalInt μK ψ (κ₀ * m) = ∫ x, F (x * κ₀) ∂μK := by
      unfold zonalInt
      rw [← integral_indicator hKm]
      congr 1; funext x
      by_cases hx : x ∈ KO k (Fin N)
      · have hx' : x * κ₀ ∈ KO k (Fin N) := mul_mem hx hκ₀
        rw [hFdef, Set.indicator_of_mem (SetLike.mem_coe.2 hx), Set.indicator_of_mem (SetLike.mem_coe.2 hx'), mul_assoc]
      · have hx' : x * κ₀ ∉ KO k (Fin N) := fun h => hx ((Subgroup.mul_mem_cancel_right _ hκ₀).1 h)
        rw [hFdef, Set.indicator_of_notMem (fun h => hx (SetLike.mem_coe.1 h)),
          Set.indicator_of_notMem (fun h => hx' (SetLike.mem_coe.1 h))]
    have e2 : zonalInt μK ψ m = ∫ x, F x ∂μK := by
      unfold zonalInt; rw [← integral_indicator hKm]
    have e3 : ∫ x, F (x * κ₀) ∂μK = ∫ x, F x ∂ν :=
      (integral_map (measurable_mul_const κ₀).aemeasurable hF.aestronglyMeasurable).symm
    have hIν : Integrable F ν := hF.integrable_of_hasCompactSupport hFs
    have hIμ : Integrable F μK := hF.integrable_of_hasCompactSupport hFs
    have Lre := L (fun x => (F x).re) (Complex.continuous_re.comp hF) (hFs.comp_left Complex.zero_re)
    have Lim := L (fun x => (F x).im) (Complex.continuous_im.comp hF) (hFs.comp_left Complex.zero_im)
    rw [hc1, one_smul] at Lre Lim
    have e4 : ∫ x, F x ∂ν = ∫ x, F x ∂μK := by
      apply Complex.ext
      · have a := integral_re hIν
        have b := integral_re hIμ
        simp only [RCLike.re_to_complex] at a b
        rw [← a, ← b, Lre]
      · have a := integral_im hIν
        have b := integral_im hIμ
        simp only [RCLike.im_to_complex] at a b
        rw [← a, ← b, Lim]
    rw [e1, e3, e4, e2]
  · unfold zonalInt
    congr 1; funext κ
    rw [← mul_assoc, hψ _ _ hκ₀]

end GlobalTheory.ZonalBi
