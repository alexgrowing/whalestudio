import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.KerNIdA

noncomputable section

open MeasureTheory Matrix Filter Topology

namespace PositivityTheory.RgBcC.VC.KN

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem nil_fix {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} {u : G n} (hu : u ∈ nilSet W₁ W₂) :
    ∀ v ∈ W₁, u.val *ᵥ v = v := by
  intro v hv
  have h := hu.2.2 v hv
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h
  exact h

theorem nil_mem₂ {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (hW : W₁ ≤ W₂) {u : G n} (hu : u ∈ nilSet W₁ W₂) :
    ∀ v ∈ W₂, u.val *ᵥ v ∈ W₂ := by
  intro v hv
  have h := W₂.add_mem (hu.1 v) hv
  rwa [Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel] at h

theorem nil_maps {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (hW : W₁ ≤ W₂) {u : G n} (hu : u ∈ nilSet W₁ W₂)
    (hu' : u⁻¹ ∈ nilSet W₁ W₂) :
    W₁.map (Matrix.mulVecLin u.val) = W₁ ∧ W₂.map (Matrix.mulVecLin u.val) = W₂ := by
  constructor
  · apply le_antisymm
    · intro x hx
      obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hx
      rw [Matrix.mulVecLin_apply, nil_fix hu v hv]
      exact hv
    · intro v hv
      exact Submodule.mem_map.mpr ⟨v, hv, by rw [Matrix.mulVecLin_apply, nil_fix hu v hv]⟩
  · apply le_antisymm
    · intro x hx
      obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp hx
      rw [Matrix.mulVecLin_apply]
      exact nil_mem₂ hW hu v hv
    · intro v hv
      refine Submodule.mem_map.mpr ⟨u⁻¹.val *ᵥ v, nil_mem₂ hW hu' v hv, ?_⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

theorem mem_nil_of {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} {N : Subgroup (G n)} (hN : (N : Set (G n)) = nilSet W₁ W₂)
    (u : N) : (u : G n) ∈ nilSet W₁ W₂ := by
  rw [← hN]
  exact u.2

theorem maps_of {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (hW : W₁ ≤ W₂) {N : Subgroup (G n)}
    (hN : (N : Set (G n)) = nilSet W₁ W₂) (u : N) :
    W₁.map (Matrix.mulVecLin (u : G n).val) = W₁ ∧ W₂.map (Matrix.mulVecLin (u : G n).val) = W₂ := by
  refine nil_maps hW (mem_nil_of hN u) ?_
  rw [← Subgroup.coe_inv]
  exact mem_nil_of hN u⁻¹

theorem cptN (hLg : LgCpt) {N : Subgroup (G n)} (hNc : IsClosed (N : Set (G n))) (R : ℝ) :
    IsCompact {u : N | lg (u : G n).val ≤ R} :=
  hNc.isClosedEmbedding_subtypeVal.isCompact_preimage (hLg n R)

theorem mul_memGL (u : G n) (y : Mat n) (hy : y ∈ GLs n) : u.val * y ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq] at hy ⊢
  rw [Matrix.det_mul]
  exact mul_ne_zero (by simpa [GLs] using memGL u) hy

theorem integrable_N (hLg : LgCpt) [MeasurableSpace (G n)] [BorelSpace (G n)] {N : Subgroup (G n)}
    (hNc : IsClosed (N : Set (G n))) (ν : Measure N) [IsFiniteMeasureOnCompacts ν] {X : Type} [NormedAddCommGroup X]
    (h : Mat n → X) (hc : ContinuousOn h (GLs n)) (R : ℝ) (hR : ∀ y ∈ GLs n, R < lg y → h y = 0)
    (y : Mat n) (hy : y ∈ GLs n) : Integrable (fun u : N => h ((u : G n).val * y)) ν := by
  have hcont : Continuous (fun u : N => h ((u : G n).val * y)) :=
    hc.comp_continuous ((Units.continuous_val.comp continuous_subtype_val).mul continuous_const)
      (fun u => mul_memGL _ y hy)
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (cptN hLg hNc (R + lg y)) ?_
  intro u hu
  simp only [Set.mem_setOf_eq, not_le] at hu
  apply hR _ (mul_memGL _ y hy)
  have := lg_le_of_mul ((u : G n).val) y hy
  linarith

end PositivityTheory.RgBcC.VC.KN
