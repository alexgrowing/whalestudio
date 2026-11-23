import Mathlib

namespace GroundTheory.Global

open Topology Filter

def NoSmallSubgroups (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∃ U ∈ 𝓝 (1 : G), ∀ H : Subgroup G, (H : Set G) ⊆ U → H = ⊥

theorem norm_sq_sub_one_ge {z : ℂ} (hz : ‖z - 1‖ < 1 / 2) :
    3 / 2 * ‖z - 1‖ ≤ ‖z ^ 2 - 1‖ := by
  have h1 : z ^ 2 - 1 = (z - 1) * (z + 1) := by ring
  have h2 : (3 : ℝ) / 2 ≤ ‖z + 1‖ := by
    have : z + 1 = 2 - (1 - z) := by ring
    have h3 : ‖(2 : ℂ)‖ = 2 := by simp
    have h4 : ‖1 - z‖ = ‖z - 1‖ := norm_sub_rev _ _
    calc (3 : ℝ) / 2 ≤ ‖(2 : ℂ)‖ - ‖1 - z‖ := by rw [h3, h4]; linarith
      _ ≤ ‖(2 : ℂ) - (1 - z)‖ := norm_sub_norm_le _ _
      _ = ‖z + 1‖ := by rw [this]
  rw [h1, norm_mul]
  nlinarith [norm_nonneg (z - 1)]

theorem eq_one_of_forall_norm_pow_two_pow_sub_one_lt {z : ℂ}
    (hz : ∀ k : ℕ, ‖z ^ (2 ^ k) - 1‖ < 1 / 2) : z = 1 := by
  have key : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have h := norm_sq_sub_one_ge (hz k)
      rw [← pow_mul, ← pow_succ] at h
      calc (3 / 2 : ℝ) ^ (k + 1) * ‖z - 1‖ = 3 / 2 * ((3 / 2) ^ k * ‖z - 1‖) := by ring
        _ ≤ 3 / 2 * ‖z ^ (2 ^ k) - 1‖ := by gcongr
        _ ≤ _ := h
  by_contra hne
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / (2 * ‖z - 1‖)) (by norm_num : (1 : ℝ) < 3 / 2)
  have h1 := lt_of_le_of_lt (key k) (hz k)
  rw [div_lt_iff₀ (by positivity)] at hk
  nlinarith

theorem eq_one_of_sq_mem {s : Set ℂ} (hsq : ∀ z ∈ s, z ^ 2 ∈ s)
    (hs : ∀ z ∈ s, ‖z - 1‖ < 1 / 2) {z : ℂ} (hz : z ∈ s) : z = 1 := by
  refine eq_one_of_forall_norm_pow_two_pow_sub_one_lt fun k ↦ hs _ ?_
  induction k with
  | zero => simpa using hz
  | succ k ih =>
    rw [pow_succ, pow_mul]
    exact hsq _ ih

namespace Circle

theorem subgroup_eq_bot_of_norm_sub_one_lt (H : Subgroup Circle)
    (hH : ∀ z ∈ H, ‖(z : ℂ) - 1‖ < 1 / 2) : H = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot, ← Circle.coe_eq_one]
  refine eq_one_of_sq_mem (s := (↑) '' (H : Set Circle)) ?_ ?_ ⟨z, hz, rfl⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact ⟨w ^ 2, H.pow_mem hw 2, by simp⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact hH w hw

theorem noSmallSubgroups : NoSmallSubgroups Circle := by
  refine ⟨{z : Circle | ‖(z : ℂ) - 1‖ < 1 / 2}, ?_, fun H hH ↦
    subgroup_eq_bot_of_norm_sub_one_lt H fun z hz ↦ hH hz⟩
  have hc : Continuous fun z : Circle ↦ ‖(z : ℂ) - 1‖ :=
    (continuous_subtype_val.sub continuous_const).norm
  exact (isOpen_lt hc continuous_const).mem_nhds (by simp)

end Circle

namespace Complex

theorem units_subgroup_eq_bot_of_norm_sub_one_lt (H : Subgroup ℂˣ)
    (hH : ∀ z ∈ H, ‖(z : ℂ) - 1‖ < 1 / 2) : H = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot, ← Units.val_eq_one]
  refine eq_one_of_sq_mem (s := (↑) '' (H : Set ℂˣ)) ?_ ?_ ⟨z, hz, rfl⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact ⟨w ^ 2, H.pow_mem hw 2, by simp⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact hH w hw

theorem units_noSmallSubgroups : NoSmallSubgroups ℂˣ := by
  refine ⟨{z : ℂˣ | ‖(z : ℂ) - 1‖ < 1 / 2}, ?_, fun H hH ↦
    units_subgroup_eq_bot_of_norm_sub_one_lt H fun z hz ↦ hH hz⟩
  have hc : Continuous fun z : ℂˣ ↦ ‖(z : ℂ) - 1‖ :=
    (Units.continuous_val.sub continuous_const).norm
  exact (isOpen_lt hc continuous_const).mem_nhds (by simp)

end Complex

section Kernel

variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H]

theorem isOpen_ker_of_noSmallSubgroups
    (hG : ∀ W ∈ 𝓝 (1 : G), ∃ V : OpenSubgroup G, (V : Set G) ⊆ W) (hH : NoSmallSubgroups H)
    (f : G →* H) (hf : Continuous f) : IsOpen (f.ker : Set G) := by
  obtain ⟨U, hU, hsmall⟩ := hH
  have hW : f ⁻¹' U ∈ 𝓝 (1 : G) := hf.continuousAt.preimage_mem_nhds (by rwa [map_one])
  obtain ⟨V, hV⟩ := hG _ hW
  have hmap : V.toSubgroup.map f = ⊥ := by
    refine hsmall _ ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hV hx
  refine Subgroup.isOpen_mono (H₁ := V.toSubgroup) ?_ V.isOpen
  rwa [← Subgroup.map_eq_bot_iff]

theorem exists_openSubgroup_subset_of_profinite [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G] {W : Set G} (hW : W ∈ 𝓝 (1 : G)) :
    ∃ V : OpenSubgroup G, (V : Set G) ⊆ W := by
  obtain ⟨C, ⟨hC1, hCc⟩, hCW⟩ := (nhds_basis_clopen (1 : G)).mem_iff.1 hW
  obtain ⟨V, hV⟩ := IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one hCc hC1
  exact ⟨V, hV.trans hCW⟩

variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

theorem isOpen_ker_of_profinite (hH : NoSmallSubgroups H) (f : G →* H) (hf : Continuous f) :
    IsOpen (f.ker : Set G) :=
  isOpen_ker_of_noSmallSubgroups (fun _ hW ↦ exists_openSubgroup_subset_of_profinite hW) hH f hf

theorem finite_range_of_profinite (hH : NoSmallSubgroups H) (f : G →* H) (hf : Continuous f) :
    Finite f.range :=
  have : Finite (G ⧸ f.ker) :=
    Subgroup.quotient_finite_of_isOpen _ (isOpen_ker_of_profinite hH f hf)
  Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange f).toEquiv

theorem isOpen_ker_of_profinite_circle (f : G →* Circle) (hf : Continuous f) :
    IsOpen (f.ker : Set G) :=
  isOpen_ker_of_profinite Circle.noSmallSubgroups f hf

theorem finite_range_of_profinite_circle (f : G →* Circle) (hf : Continuous f) :
    Finite f.range :=
  finite_range_of_profinite Circle.noSmallSubgroups f hf

theorem isOpen_ker_of_profinite_units_complex (f : G →* ℂˣ) (hf : Continuous f) :
    IsOpen (f.ker : Set G) :=
  isOpen_ker_of_profinite Complex.units_noSmallSubgroups f hf

theorem finite_range_of_profinite_units_complex (f : G →* ℂˣ) (hf : Continuous f) :
    Finite f.range :=
  finite_range_of_profinite Complex.units_noSmallSubgroups f hf

end Kernel

end GroundTheory.Global
