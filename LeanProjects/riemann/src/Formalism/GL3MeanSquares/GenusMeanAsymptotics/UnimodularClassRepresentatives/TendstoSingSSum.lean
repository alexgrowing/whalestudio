import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoSumBoxIdeal
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AlphaNOfVdZeroUnit
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LValEtaEqLValEtaF
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.TendstoWeightedTprod
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ALocEqRoL

open NumberField Module Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

namespace A5

open scoped Classical in
theorem coe_filter_box (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (T : ℝ)
    (v : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} →₀ ℕ) :
    {n : 𝓞 F | n ∈ boxSet K F T ∧ n ∈ bId v} =
      ↑((boxSet_finite hK hF T).toFinset.filter fun n => v ≤ valF n) := by
  ext n
  simp only [Set.mem_setOf_eq, Finset.coe_filter, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨hb, hI⟩
    exact ⟨hb, (mem_bId_iff (ne_zero_of_mem_boxSet hb) v).mp hI⟩
  · rintro ⟨hb, hv⟩
    exact ⟨hb, (mem_bId_iff (ne_zero_of_mem_boxSet hb) v).mpr hv⟩

open scoped Classical in
theorem dominated (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V)
    (S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) :
    ∃ C : ℝ, ∀ T : ℝ, 1 ≤ T → ∀ v : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} →₀ ℕ,
      |T ^ (-((Formalism.HermitianLatticesTheory.fDeg K * finrank K V : ℕ) : ℤ)) *
        ∑ n ∈ (boxSet_finite hK hF T).toFinset.filter (fun n => v ≤ valF n),
          (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (finrank K V - 1) * ∏ 𝔭 ∈ S, aLoc h L 𝔭 n| ≤
        C / nrm (fun 𝔭 => (Ideal.absNorm 𝔭.1 : ℝ)) v := by
  obtain ⟨C1, hC1⟩ := prodS_bound hK hF hs hd hL hLi hm S
  refine ⟨2 ^ Formalism.HermitianLatticesTheory.fDeg K * C1, fun T hT v => ?_⟩
  have hT0 : 0 < T := lt_of_lt_of_le one_pos hT
  have hsum0 : 0 ≤ ∑ n ∈ (boxSet_finite hK hF T).toFinset.filter (fun n => v ≤ valF n),
      (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (finrank K V - 1) * ∏ 𝔭 ∈ S, aLoc h L 𝔭 n := by
    refine Finset.sum_nonneg fun n hn => ?_
    have hb : n ∈ boxSet K F T := by
      simpa using (Finset.mem_filter.mp hn).1
    exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (hC1 n (ne_zero_of_mem_boxSet hb)).1
  rw [abs_of_nonneg (mul_nonneg (zpow_nonneg hT0.le _) hsum0)]
  have hterm : ∀ n ∈ (boxSet_finite hK hF T).toFinset.filter (fun n => v ≤ valF n),
      (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (finrank K V - 1) * ∏ 𝔭 ∈ S, aLoc h L 𝔭 n ≤
        (T ^ Formalism.HermitianLatticesTheory.fDeg K) ^ (finrank K V - 1) * C1 := fun n hn => by
    have hb : n ∈ boxSet K F T := by
      simpa using (Finset.mem_filter.mp hn).1
    have hP := hC1 n (ne_zero_of_mem_boxSet hb)
    exact mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) (absNorm_le_of_mem_boxSet hK hF hb) _) hP.2 hP.1
      (pow_nonneg (pow_nonneg hT0.le _) _)
  have hcard : (((boxSet_finite hK hF T).toFinset.filter (fun n => v ≤ valF n)).card : ℝ) ≤
      2 ^ Formalism.HermitianLatticesTheory.fDeg K * T ^ Formalism.HermitianLatticesTheory.fDeg K / (Ideal.absNorm (bId v) : ℝ) := by
    have h1 := Formalism.HermitianLattices.Ext.L3.BoxCube.card_box_le hK hF (bId_ne_bot v) hT0.le
    have h2 : ((boxSet_finite hK hF T).toFinset.filter (fun n => v ≤ valF n)).card =
        Nat.card {n : 𝓞 F // n ∈ boxSet K F T ∧ n ∈ bId v} := by
      rw [← Set.ncard_coe_finset, ← coe_filter_box hK hF T v, ← Nat.card_coe_set_eq]
      rfl
    rw [h2]
    exact h1
  have hle := Finset.sum_le_card_nsmul _ _ _ hterm
  rw [nsmul_eq_mul] at hle
  have hexp : Formalism.HermitianLatticesTheory.fDeg K * finrank K V =
      Formalism.HermitianLatticesTheory.fDeg K + Formalism.HermitianLatticesTheory.fDeg K * (finrank K V - 1) := by
    conv_lhs => rw [show finrank K V = (finrank K V - 1) + 1 by omega]
    ring
  have hTT : T ^ (-((Formalism.HermitianLatticesTheory.fDeg K * finrank K V : ℕ) : ℤ)) *
      (T ^ Formalism.HermitianLatticesTheory.fDeg K * (T ^ Formalism.HermitianLatticesTheory.fDeg K) ^ (finrank K V - 1)) = 1 := by
    rw [zpow_neg, zpow_natCast, ← pow_mul, ← pow_add, ← hexp]
    exact inv_mul_cancel₀ (pow_ne_zero _ hT0.ne')
  have hC1n : 0 ≤ C1 := by
    have := hC1 1 one_ne_zero
    exact this.1.trans this.2
  rw [← absNorm_bId]
  calc T ^ (-((Formalism.HermitianLatticesTheory.fDeg K * finrank K V : ℕ) : ℤ)) *
        ∑ n ∈ (boxSet_finite hK hF T).toFinset.filter (fun n => v ≤ valF n),
          (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (finrank K V - 1) * ∏ 𝔭 ∈ S, aLoc h L 𝔭 n
      ≤ T ^ (-((Formalism.HermitianLatticesTheory.fDeg K * finrank K V : ℕ) : ℤ)) *
        ((2 ^ Formalism.HermitianLatticesTheory.fDeg K * T ^ Formalism.HermitianLatticesTheory.fDeg K / (Ideal.absNorm (bId v) : ℝ)) *
          ((T ^ Formalism.HermitianLatticesTheory.fDeg K) ^ (finrank K V - 1) * C1)) := by
        refine mul_le_mul_of_nonneg_left (hle.trans ?_) (zpow_nonneg hT0.le _)
        exact mul_le_mul_of_nonneg_right hcard
          (mul_nonneg (pow_nonneg (pow_nonneg hT0.le _) _) hC1n)
    _ = (2 ^ Formalism.HermitianLatticesTheory.fDeg K * C1 / (Ideal.absNorm (bId v) : ℝ)) *
        (T ^ (-((Formalism.HermitianLatticesTheory.fDeg K * finrank K V : ℕ) : ℤ)) *
          (T ^ Formalism.HermitianLatticesTheory.fDeg K * (T ^ Formalism.HermitianLatticesTheory.fDeg K) ^ (finrank K V - 1))) := by ring
    _ = 2 ^ Formalism.HermitianLatticesTheory.fDeg K * C1 / (Ideal.absNorm (bId v) : ℝ) := by rw [hTT, mul_one]

end A5

open A5 in
theorem tendsto_singS_sum (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hm : 2 ≤ finrank K V) :
    Tendsto (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * finrank K V : ℕ) : ℤ)) *
        ∑ᶠ n ∈ boxSet K F ((j : ℝ) ^ 2),
          (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (finrank K V - 1) * singS F h L n)
      atTop (𝓝 ((finrank K V : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
        Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) * lValEtaF K F (finrank K V))) := by
  classical
  set S : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} :=
    (finite_vd_ne_zero (F := F) hK hF hs hd hL hLi).toFinset with hSdef
  have hS : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, vd h L 𝔭.1 ≠ 0 → 𝔭 ∈ S := fun 𝔭 h𝔭 =>
    (Set.Finite.mem_toFinset _).mpr h𝔭
  obtain ⟨C, hC⟩ := dominated hK hF hs hd hL hLi hm S
  set c0 : ℝ := (finrank K V : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
    Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) with hc0
  have main := tendsto_weighted_tprod
    (q := fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} => (Ideal.absNorm 𝔭.1 : ℝ))
    (fun 𝔭 => by exact_mod_cast two_le_absNorm 𝔭.2) summable_inv_absNorm_sq S
    (ρ := roL h L S) (roL_zero hK hF hs hd hL hLi hm hS) (fun 𝔭 h𝔭 j => by simp [roL, h𝔭])
    (roL_diff hK hF hs hd hL hLi hm hS) valF
    (fun j : ℕ => (boxSet_finite hK hF ((j : ℝ) ^ 2)).toFinset)
    (fun n => (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (finrank K V - 1) * ∏ 𝔭 ∈ S, aLoc h L 𝔭 n)
    (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * finrank K V : ℕ) : ℤ)))
    (c0 * ∏ 𝔭 ∈ S, (eFac K (finrank K V) 𝔭.1)⁻¹) c0 C
    (fun 𝔭 => (eFac K (finrank K V) 𝔭.1)⁻¹) (fun h0 => by rw [h0, zero_mul]) ?_ ?_ ?_
  · refine main.congr fun j => ?_
    rw [finsum_mem_eq_finite_toFinset_sum _ (boxSet_finite hK hF ((j : ℝ) ^ 2))]
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    have hb : n ∈ boxSet K F ((j : ℝ) ^ 2) := (Set.Finite.mem_toFinset _).mp hn
    rw [singS_eq hK hF hs hd hL hLi hm hS (ne_zero_of_mem_boxSet hb), mul_assoc]
  · intro v hv
    have ht := tendsto_sum_box_ideal hK hF hs hd hL hLi hm S hS (bId_ne_bot v)
      (fun 𝔭 h𝔭 => bId_sup_eq_top (Finset.disjoint_right.mp hv h𝔭))
    simp_rw [coe_filter_box hK hF, finsum_mem_coe_finset] at ht
    rw [absNorm_bId] at ht
    have he : c0 * (∏ 𝔭 ∈ S, (eFac K (finrank K V) 𝔭.1)⁻¹) /
        nrm (fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} => (Ideal.absNorm 𝔭.1 : ℝ)) v =
        c0 / nrm (fun 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} => (Ideal.absNorm 𝔭.1 : ℝ)) v *
          ∏ 𝔭 ∈ S, (eFac K (finrank K V) 𝔭.1)⁻¹ := by ring
    rw [he]
    exact ht
  · filter_upwards [eventually_ge_atTop 1] with j hj v
    refine hC _ ?_ v
    have : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    nlinarith
  · intro S' hS'
    have ht := tendsto_sum_box_ideal hK hF hs hd hL hLi hm S' (fun 𝔭 h𝔭 => hS' (hS 𝔭 h𝔭))
      (b := ⊤) (by simp) (fun 𝔭 _ => by simp)
    simp only [Submodule.mem_top, and_true, Ideal.absNorm_top, Nat.cast_one, div_one] at ht
    refine ht.congr fun j => ?_
    have hset : {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2)} = boxSet K F ((j : ℝ) ^ 2) := rfl
    rw [hset, finsum_mem_eq_finite_toFinset_sum _ (boxSet_finite hK hF ((j : ℝ) ^ 2))]
    congr 1
    refine Finset.sum_congr rfl fun n hn => ?_
    have hb : n ∈ boxSet K F ((j : ℝ) ^ 2) := (Set.Finite.mem_toFinset _).mp hn
    rw [mul_assoc, ← prod_aLoc hK hF hs hd hL hLi hS hS' (ne_zero_of_mem_boxSet hb)]
    rfl

end Formalism.HermitianLattices.Ext.L3
