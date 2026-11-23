import Mathlib

noncomputable section

open MeasureTheory Topology Filter
open scoped ENNReal NNReal Pointwise

namespace Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.Modular

variable {G : Type*} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

local notation "Δ" => Measure.modularCharacterFun (G := G)

theorem map_right (g : G) : (Measure.haar : Measure G).map (· * g) = Δ g • (Measure.haar : Measure G) :=
  Measure.map_right_mul_eq_modularCharacterFun_smul _ g

theorem haar_preimage (g : G) {A : Set G} (hA : MeasurableSet A) :
    (Measure.haar : Measure G) ((· * g) ⁻¹' A) = (Δ g : ℝ≥0∞) * (Measure.haar : Measure G) A := by
  have h : ((Measure.haar : Measure G).map (· * g)) A = (Δ g • (Measure.haar : Measure G)) A := by rw [map_right]
  rw [Measure.map_apply (measurable_mul_const g) hA] at h
  rw [h, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]

theorem exists_compact_pos : ∃ C : Set G, IsCompact C ∧ 0 < (Measure.haar : Measure G) C ∧
    (Measure.haar : Measure G) C ≠ ⊤ := by
  obtain ⟨C, hC, h1⟩ := exists_compact_mem_nhds (1 : G)
  refine ⟨C, hC, ?_, hC.measure_lt_top.ne⟩
  exact Measure.measure_pos_of_nonempty_interior _ ⟨1, mem_interior_iff_mem_nhds.2 h1⟩

theorem eq_one_of_zpow_mem {k : G} {Q : Set G} (hQ : IsCompact Q) (hk : ∀ j : ℤ, k ^ j ∈ Q) : Δ k = 1 := by
  obtain ⟨C, hC, hpos, hfin⟩ := exists_compact_pos (G := G)
  have hCQ : IsCompact (C * Q⁻¹) := hC.mul hQ.inv
  set M := (Measure.haar : Measure G) (C * Q⁻¹) with hM
  have hMfin : M ≠ ⊤ := hCQ.measure_lt_top.ne
  have hbound : ∀ j : ℤ, ((Δ k ^ j : ℝ≥0) : ℝ≥0∞) * (Measure.haar : Measure G) C ≤ M := by
    intro j
    have hsub : (· * k ^ j) ⁻¹' C ⊆ C * Q⁻¹ := by
      intro x hx
      refine ⟨x * k ^ j, hx, (k ^ j)⁻¹, Set.inv_mem_inv.2 (hk j), by group⟩
    have := haar_preimage (k ^ j) hC.isClosed.measurableSet
    have hz : Δ (k ^ j) = Δ k ^ j := map_zpow (Measure.modularCharacter (G := G)) k j
    rw [hz] at this
    calc ((Δ k ^ j : ℝ≥0) : ℝ≥0∞) * (Measure.haar : Measure G) C
        = (Measure.haar : Measure G) ((· * k ^ j) ⁻¹' C) := by rw [this]
      _ ≤ M := measure_mono hsub
  have hx : 0 < (Δ k : ℝ) := by exact_mod_cast Measure.modularCharacterFun_pos k
  set B := M.toReal / ((Measure.haar : Measure G) C).toReal with hB
  have hCr : 0 < ((Measure.haar : Measure G) C).toReal := ENNReal.toReal_pos hpos.ne' hfin
  have hb : ∀ j : ℤ, (Δ k : ℝ) ^ j ≤ B := by
    intro j
    have h1 := hbound j
    rw [hB, le_div_iff₀ hCr]
    have h2 := (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin) hMfin).2 h1
    rw [ENNReal.toReal_mul] at h2
    simpa using h2
  by_contra hne
  rcases lt_or_gt_of_ne (show (Δ k : ℝ) ≠ 1 from fun h => hne (by exact_mod_cast h)) with hlt | hgt
  · have ht : Tendsto (fun j : ℕ => ((Δ k : ℝ)⁻¹) ^ j) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (one_lt_inv₀ hx |>.2 hlt)
    obtain ⟨j, hj⟩ := (ht.eventually_gt_atTop B).exists
    have := hb (-(j : ℤ))
    rw [zpow_neg, zpow_natCast, ← inv_pow] at this
    linarith
  · have ht : Tendsto (fun j : ℕ => (Δ k : ℝ) ^ j) atTop atTop := tendsto_pow_atTop_atTop_of_one_lt hgt
    obtain ⟨j, hj⟩ := (ht.eventually_gt_atTop B).exists
    have := hb (j : ℤ)
    rw [zpow_natCast] at this
    linarith

theorem eventually_lt (ε : ℝ) (hε : 0 < ε) : ∀ᶠ h in 𝓝 (1 : G), (Δ h : ℝ) < 1 + ε := by
  obtain ⟨C, hC, hpos, hfin⟩ := exists_compact_pos (G := G)
  have hlt : (Measure.haar : Measure G) C < ENNReal.ofReal (1 + ε) * (Measure.haar : Measure G) C := by
    have h1 : (1 : ℝ≥0∞) < ENNReal.ofReal (1 + ε) := by
      rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
    have := ENNReal.mul_lt_mul_right hpos.ne' hfin h1
    simpa [mul_comm] using this
  obtain ⟨U, hCU, hU, hUlt⟩ := Set.exists_isOpen_lt_of_lt C _ hlt
  obtain ⟨V, hV, hCV⟩ := compact_open_separated_mul_right hC hU hCU
  have hV' : ∀ᶠ h in 𝓝 (1 : G), h⁻¹ ∈ V := by
    have ht : Tendsto (fun h : G => h⁻¹) (𝓝 1) (𝓝 1) := by simpa using continuous_inv.tendsto (1 : G)
    exact ht hV
  filter_upwards [hV'] with h hh
  have hsub : (· * h) ⁻¹' C ⊆ U := by
    intro x hx
    apply hCV
    exact ⟨x * h, hx, h⁻¹, hh, by group⟩
  have h2 : (Δ h : ℝ≥0∞) * (Measure.haar : Measure G) C < ENNReal.ofReal (1 + ε) * (Measure.haar : Measure G) C := by
    rw [← haar_preimage h hC.isClosed.measurableSet]
    exact lt_of_le_of_lt (measure_mono hsub) hUlt
  have h3 : (Δ h : ℝ≥0∞) < ENNReal.ofReal (1 + ε) :=
    not_le.1 fun hle => lt_irrefl _ (lt_of_le_of_lt (mul_le_mul_of_nonneg_right hle zero_le) h2)
  rw [← ENNReal.ofReal_coe_nnreal] at h3
  exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).1 h3

theorem comp_aut (α : G ≃ₜ* G) (g : G) : Δ (α g) = Δ g := by
  obtain ⟨C, hC, hpos, hfin⟩ := exists_compact_pos (G := G)
  have hmeas : Measurable α := α.continuous.measurable
  have : ((Measure.haar : Measure G).map α).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map _ α
  set c := ((Measure.haar : Measure G).map α).haarScalarFactor Measure.haar with hc
  have hcpos : 0 < c := Measure.haarScalarFactor_pos_of_isHaarMeasure _ _
  have hmap : (Measure.haar : Measure G).map α = c • Measure.haar :=
    Measure.isMulLeftInvariant_eq_smul _ _
  have key : ((Measure.haar : Measure G).map α).map (· * α g) = ((Measure.haar : Measure G).map (· * g)).map α := by
    rw [Measure.map_map (measurable_mul_const _) hmeas, Measure.map_map hmeas (measurable_mul_const _)]
    congr 1
    funext x
    simp [map_mul]
  rw [hmap, map_right, Measure.map_smul, Measure.map_smul, map_right, hmap, smul_smul, smul_smul] at key
  have := congrArg (fun μ : Measure G => μ C) key
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at this
  have hcC : ((c * Δ (α g) : ℝ≥0) : ℝ≥0∞) = ((Δ g * c : ℝ≥0) : ℝ≥0∞) :=
    (ENNReal.mul_left_inj hpos.ne' hfin).1 (by simpa [ENNReal.coe_mul] using this)
  have h2 : c * Δ (α g) = Δ g * c := by exact_mod_cast hcC
  rw [mul_comm (Δ g)] at h2
  exact mul_left_cancel₀ hcpos.ne' h2

theorem eq_one_of_iterate (α : G ≃ₜ* G) (g k : G) (hk : Δ k = 1)
    (hlim : Tendsto (fun m : ℕ => (⇑α)^[m] g) atTop (𝓝 k)) : Δ g = 1 := by
  have hit : ∀ m : ℕ, Δ ((⇑α)^[m] g) = Δ g := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', comp_aut, ih]
  set hseq := fun m : ℕ => k⁻¹ * (⇑α)^[m] g with hh
  have hlim1 : Tendsto hseq atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := k⁻¹)).mul hlim
    simpa using this
  have hval : ∀ m, Δ (hseq m) = Δ g := fun m => by
    simp only [hh, Measure.modularCharacterFun_map_mul, hit]
    have : Δ k⁻¹ = 1 := by
      have h1 := Measure.modularCharacterFun_map_mul (G := G) k⁻¹ k
      rw [inv_mul_cancel, Measure.modularCharacterFun_map_one, hk, mul_one] at h1
      exact h1.symm
    rw [this, one_mul]
  have hvalinv : ∀ m, Δ (hseq m)⁻¹ * Δ g = 1 := fun m => by
    rw [← hval m, ← Measure.modularCharacterFun_map_mul, inv_mul_cancel, Measure.modularCharacterFun_map_one]
  have hx : 0 < (Δ g : ℝ) := by exact_mod_cast Measure.modularCharacterFun_pos g
  by_contra hne
  rcases lt_or_gt_of_ne (show (Δ g : ℝ) ≠ 1 from fun h => hne (by exact_mod_cast h)) with hlt | hgt
  ·
    have hlim2 : Tendsto (fun m => (hseq m)⁻¹) atTop (𝓝 1) := by simpa using hlim1.inv
    have hε : 0 < (Δ g : ℝ)⁻¹ - 1 := by rw [sub_pos]; exact (one_lt_inv₀ hx).2 hlt
    obtain ⟨m, hm⟩ := (hlim2.eventually (eventually_lt _ hε)).exists
    have h1 := hvalinv m
    have h2 : (Δ (hseq m)⁻¹ : ℝ) * Δ g = 1 := by exact_mod_cast h1
    have h3 : (Δ (hseq m)⁻¹ : ℝ) = (Δ g : ℝ)⁻¹ := by field_simp; linarith
    linarith
  · have hε : 0 < (Δ g : ℝ) - 1 := by linarith
    obtain ⟨m, hm⟩ := (hlim1.eventually (eventually_lt _ hε)).exists
    have := hval m
    rw [show (Δ (hseq m) : ℝ) = Δ g by exact_mod_cast this] at hm
    linarith

end Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.Modular
