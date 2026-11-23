import Mathlib

theorem UpperTheory.Reformulated.B.Qi19.tube.{u_1, u_2} :
    ∀ {G : Type u_1} {X : Type u_2} [inst : Group G] [inst_1 : TopologicalSpace G] [ContinuousInv G]
    [inst_3 : TopologicalSpace X] (T : G → X → X),
    (Continuous fun (p : G × X) ↦ T p.1 p.2) →
      (∀ (w : X), T (1 : G) w = w) →
        (∀ (k : G) (w : X), T k⁻¹ (T k w) = w) →
          ∀ {g : X → ℂ},
            IsLocallyConstant g → HasCompactSupport g → ∀ᶠ (k : G) in nhds (1 : G), ∀ (w : X), g (T k w) = g w := by
  intro G X _ _ _ _ T hT h1 hinv g hg hc
  have hK : ∀ᶠ k : G in nhds (1 : G), ∀ w ∈ tsupport g, g (T k w) = g w := by
    refine IsCompact.eventually_forall_of_forall_eventually
      (P := fun (k : G) (w : X) => g (T k w) = g w) hc.isCompact ?_
    intro y _
    have ha := (hg.comp_continuous hT).eventually_eq ((1 : G), y)
    have hb := (hg.comp_continuous (continuous_snd : Continuous fun p : G × X => p.2)).eventually_eq
      ((1 : G), y)
    filter_upwards [ha, hb] with z hza hzb
    simp only [Function.comp_apply, h1] at hza hzb
    rw [hza, hzb]
  have hi : Filter.Tendsto (fun k : G => k⁻¹) (nhds 1) (nhds 1) := by
    simpa using (continuous_inv (G := G)).tendsto 1
  filter_upwards [hK, hi.eventually hK] with k hk hk' w
  by_cases hw : w ∈ tsupport g
  · exact hk w hw
  · by_cases hw' : T k w ∈ tsupport g
    · have h := hk' _ hw'
      rw [hinv] at h
      exact h.symm
    · rw [image_eq_zero_of_notMem_tsupport hw, image_eq_zero_of_notMem_tsupport hw']
