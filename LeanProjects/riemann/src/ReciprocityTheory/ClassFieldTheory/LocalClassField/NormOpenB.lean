import Mathlib
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecDefs
import ReciprocityTheory.ClassFieldTheory.LocalClassField.GalBasic
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ValUnitsG

namespace ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh Function
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
variable {p K L}

theorem norm_coe_K (x : K) : ‖(x : PadicAlgCl p)‖ = ‖x‖ := rfl

theorem UK_eq_preimage : (UK p K : Set Kˣ) = Units.val ⁻¹' Metric.sphere (0 : K) 1 := by
  ext x
  simp only [Set.mem_preimage, mem_sphere_zero_iff_norm]
  rfl

theorem image_UK : Units.val '' (UK p K : Set Kˣ) = Metric.sphere (0 : K) 1 := by
  rw [UK_eq_preimage, Set.image_preimage_eq_iff]
  intro x hx
  have hx' : ‖x‖ = 1 := by simpa using hx
  have h0 : x ≠ 0 := by
    rintro rfl
    simp at hx'
  exact ⟨Units.mk0 x h0, rfl⟩

theorem isCompact_UK' (hK : FiniteDimensional ℚ_[p] K) : IsCompact (UK p K : Set Kˣ) := by
  have : ProperSpace K := FiniteDimensional.proper ℚ_[p] K
  rw [Units.isEmbedding_val₀.isCompact_iff, image_UK]
  exact isCompact_sphere _ _

theorem mem_UK_of_norm_sub_one_lt (x : Kˣ) (hx : ‖(x : K) - 1‖ < 1) : x ∈ UK p K := by
  show ‖((x : K) : PadicAlgCl p)‖ = 1
  rw [norm_coe_K]
  have h := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := (x : K) - 1) (y := 1)
    (by rw [norm_one]; exact hx.ne)
  rw [sub_add_cancel, norm_one, max_eq_right hx.le] at h
  exact h

theorem mem_nhds_one_iff (S : Set Kˣ) :
    S ∈ nhds (1 : Kˣ) ↔ ∃ ε > 0, ∀ x : Kˣ, ‖(x : K) - 1‖ < ε → x ∈ S := by
  rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap, Filter.mem_comap, Units.val_one]
  constructor
  · rintro ⟨t, ht, hts⟩
    obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.1 ht
    refine ⟨ε, hε, fun x hx => hts (hb ?_)⟩
    rw [Metric.mem_ball, dist_eq_norm]; exact hx
  · rintro ⟨ε, hε, h⟩
    refine ⟨Metric.ball 1 ε, Metric.ball_mem_nhds _ hε, fun x hx => h x ?_⟩
    have : (x : K) ∈ Metric.ball (1 : K) ε := hx
    rwa [Metric.mem_ball, dist_eq_norm] at this

theorem isOpen_UKi (i : ℕ) : IsOpen (UKi p K i : Set Kˣ) := by
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  rw [mem_nhds_one_iff]
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  refine ⟨min 1 ((p : ℝ) ^ (- (i : ℝ) / eK p K)), lt_min one_pos (Real.rpow_pos_of_pos hp _), fun x hx => ?_⟩
  exact (mem_UKi_iff p K i x).2 ⟨mem_UK_of_norm_sub_one_lt x (hx.trans_le (min_le_left _ _)),
    (hx.trans_le (min_le_right _ _)).le⟩

theorem isOpen_range_pow' (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    IsOpen ((powMonoidHom n : Kˣ →* Kˣ).range : Set Kˣ) := by
  have : CompleteSpace K := FiniteDimensional.complete ℚ_[p] K
  apply Subgroup.isOpen_of_mem_nhds (g := 1)
  have hd : HasStrictDerivAt (fun x : K => x ^ n) ((n : K) * 1 ^ (n - 1)) 1 := hasStrictDerivAt_pow n 1
  have hne : ((n : K) * 1 ^ (n - 1)) ≠ 0 := by
    rw [one_pow, mul_one]; exact_mod_cast hn.ne'
  have hm := hd.map_nhds_eq hne
  simp only [one_pow] at hm
  have hr : Set.range (fun x : K => x ^ n) ∈ nhds (1 : K) := by
    rw [← hm]; exact Filter.range_mem_map
  rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap, Filter.mem_comap, Units.val_one]
  refine ⟨_, hr, ?_⟩
  rintro y ⟨x, hx⟩
  have hx' : x ^ n = (y : K) := hx
  have h0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hx'
    exact y.ne_zero hx'.symm
  exact ⟨Units.mk0 x h0, Units.ext (by simpa using hx')⟩

theorem finiteIndex_of_isOpen_of_vK (hK : FiniteDimensional ℚ_[p] K) (H : Subgroup Kˣ)
    (hH : IsOpen (H : Set Kˣ)) {x : Kˣ} (hx : x ∈ H) (hv : vK p K x ≠ 0) : H.FiniteIndex := by
  obtain ⟨π, hπ⟩ := exists_vK_eq_one p K hK
  have : DiscreteTopology (Kˣ ⧸ H) := QuotientGroup.discreteTopology hH
  set m := vK p K x with hm
  let C : Set Kˣ := ⋃ j ∈ Finset.range m.natAbs, (fun u => π ^ j * u) '' (UK p K : Set Kˣ)
  have hC : IsCompact C :=
    (Finset.range m.natAbs).isCompact_biUnion fun j _ =>
      (isCompact_UK' hK).image (continuous_const.mul continuous_id)
  have hfin : ((QuotientGroup.mk : Kˣ → Kˣ ⧸ H) '' C).Finite :=
    (hC.image QuotientGroup.continuous_mk).finite_of_discrete
  have hall : (QuotientGroup.mk : Kˣ → Kˣ ⧸ H) '' C = Set.univ := by
    rw [Set.eq_univ_iff_forall]
    intro c
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective c
    have hj0 : 0 ≤ vK p K y % m := Int.emod_nonneg _ hv
    have hj1 : vK p K y % m < |m| := Int.emod_lt_abs _ hv
    set j := (vK p K y % m).toNat with hj
    have hjc : (j : ℤ) = vK p K y % m := Int.toNat_of_nonneg hj0
    set k := vK p K y / m with hk
    have hu : (π ^ j)⁻¹ * y * (x ^ k)⁻¹ ∈ UK p K := by
      rw [mem_UK_iff p K hK, vK_mul, vK_mul, vK_inv, vK_inv, vK_pow, vK_zpow, hπ, hjc, ← hm]
      have := Int.emod_add_mul_ediv (vK p K y) m
      rw [← hk] at this
      linarith [mul_comm m k]
    refine ⟨π ^ j * ((π ^ j)⁻¹ * y * (x ^ k)⁻¹), ?_, ?_⟩
    · refine Set.mem_biUnion (x := j) ?_ ⟨_, hu, rfl⟩
      rw [Finset.coe_range, Set.mem_Iio]
      have : (j : ℤ) < (m.natAbs : ℤ) := by rw [hjc, Int.natCast_natAbs]; exact hj1
      exact_mod_cast this
    · rw [QuotientGroup.eq]
      have : (π ^ j * ((π ^ j)⁻¹ * y * (x ^ k)⁻¹))⁻¹ * y = x ^ k := by group
      rw [this]
      exact H.zpow_mem hx k
  have : Finite (Kˣ ⧸ H) := by
    rw [← Set.finite_univ_iff, ← hall]; exact hfin
  exact Subgroup.finiteIndex_of_finite_quotient

theorem finiteIndex_range_pow' (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    (powMonoidHom n : Kˣ →* Kˣ).range.FiniteIndex := by
  obtain ⟨π, hπ⟩ := exists_vK_eq_one p K hK
  refine finiteIndex_of_isOpen_of_vK hK _ (isOpen_range_pow' hK hn) (x := π ^ n) ⟨π, rfl⟩ ?_
  rw [vK_pow, hπ, mul_one]
  exact_mod_cast hn.ne'

end ReciprocityTheory.DiscreteGroups.LocalClassField
