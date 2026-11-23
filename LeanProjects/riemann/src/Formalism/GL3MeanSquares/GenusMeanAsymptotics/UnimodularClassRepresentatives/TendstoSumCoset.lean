import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemIdealLatticeIff

open NumberField Module Filter Topology
open scoped Classical

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BoxSum

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem finite_box_inter (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (T : ℝ) (A : Set (𝓞 F)) :
    {n : 𝓞 F | n ∈ boxSet K F T ∧ n ∈ A}.Finite := (finite_boxSet hK hF T).subset fun _ hn => hn.1

theorem sum_le_sum_shift (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (m : ℕ) {A B : Set (𝓞 F)}
    {T T' : ℝ} (y : 𝓞 F) (hy0 : ∀ w, 0 ≤ rEmb w y) (hyT : ∀ w, rEmb w y + T ≤ T')
    (hAB : ∀ n ∈ A, n + y ∈ B) :
    ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F T ∧ n ∈ A}, (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) ≤
      ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F T' ∧ n ∈ B},
        (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) := by
  classical
  have hA := finite_box_inter hK hF T A
  have hB := finite_box_inter hK hF T' B
  rw [finsum_mem_eq_finite_toFinset_sum _ hA, finsum_mem_eq_finite_toFinset_sum _ hB]
  have key : ∀ n ∈ hA.toFinset, n + y ∈ hB.toFinset ∧
      (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) ≤
        (Ideal.absNorm (Ideal.span {n + y}) : ℝ) ^ (m - 1) := by
    intro n hn
    rw [Set.Finite.mem_toFinset] at hn
    obtain ⟨hnb, hnA⟩ := hn
    have hb : ∀ w, 0 < rEmb w n ∧ rEmb w n ≤ T := (mem_boxSet_iff hK hF).1 hnb
    have hny : n + y ∈ boxSet K F T' := by
      rw [mem_boxSet_iff hK hF]
      intro w
      rw [map_add]
      constructor
      · linarith [(hb w).1, hy0 w]
      · linarith [(hb w).2, hyT w]
    refine ⟨by rw [Set.Finite.mem_toFinset]; exact ⟨hny, hAB n hnA⟩, ?_⟩
    have hle : (Ideal.absNorm (Ideal.span {n}) : ℝ) ≤ (Ideal.absNorm (Ideal.span {n + y}) : ℝ) := by
      rw [absNorm_eq_prod_of_mem hK hF hnb, absNorm_eq_prod_of_mem hK hF hny]
      apply Finset.prod_le_prod
      · intro w _
        exact (hb w).1.le
      · intro w _
        rw [map_add]
        linarith [hy0 w]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hle _
  calc ∑ n ∈ hA.toFinset, (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1)
      ≤ ∑ n ∈ hA.toFinset, (Ideal.absNorm (Ideal.span {n + y}) : ℝ) ^ (m - 1) :=
        Finset.sum_le_sum fun n hn => (key n hn).2
    _ = ∑ n ∈ hA.toFinset.image (· + y), (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) := by
        rw [Finset.sum_image (fun a _ b _ h => add_right_cancel h)]
    _ ≤ ∑ n ∈ hB.toFinset, (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hx
          exact (key n hn).1
        · intro _ _ _
          positivity

theorem exists_shifts {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) (x₀ : 𝓞 F) :
    ∃ (y y' : 𝓞 F) (R : ℝ), (∀ w, 0 ≤ rEmb w y ∧ rEmb w y ≤ R) ∧ (∀ w, 0 ≤ rEmb w y' ∧ rEmb w y' ≤ R) ∧
      (∀ n, n - x₀ ∈ I → n + y ∈ I) ∧ ∀ n, n ∈ I → n + y' - x₀ ∈ I := by
  classical
  have hN0 : Ideal.absNorm I ≠ 0 := fun h => hI (Ideal.absNorm_eq_zero_iff.1 h)
  have hNmem : ((Ideal.absNorm I : ℕ) : 𝓞 F) ∈ I := Ideal.absNorm_mem I
  obtain ⟨C, hCw⟩ : ∃ C : ℝ, ∀ w : {w : InfinitePlace F // w.IsReal}, |rEmb w x₀| ≤ C :=
    ⟨∑ w : {w : InfinitePlace F // w.IsReal}, |rEmb w x₀|, fun w =>
      Finset.single_le_sum (f := fun w => |rEmb w x₀|) (fun _ _ => abs_nonneg _) (Finset.mem_univ w)⟩
  obtain ⟨c, hc⟩ := exists_nat_ge C
  have hN1 : (1 : ℝ) ≤ (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 hN0
  have hcN : C ≤ ((c * Ideal.absNorm I : ℕ) : ℝ) := by
    push_cast
    have h0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
    nlinarith
  have hmem : ((c * Ideal.absNorm I : ℕ) : 𝓞 F) ∈ I := by
    rw [Nat.cast_mul]
    exact I.mul_mem_left _ hNmem
  refine ⟨((c * Ideal.absNorm I : ℕ) : 𝓞 F) - x₀, ((c * Ideal.absNorm I : ℕ) : 𝓞 F) + x₀,
    ((c * Ideal.absNorm I : ℕ) : ℝ) + C, ?_, ?_, ?_, ?_⟩
  · intro w
    rw [map_sub, map_natCast]
    have h := abs_le.1 (hCw w)
    constructor <;> linarith [h.1, h.2]
  · intro w
    rw [map_add, map_natCast]
    have h := abs_le.1 (hCw w)
    constructor <;> linarith [h.1, h.2]
  · intro n hn
    have e : n + (((c * Ideal.absNorm I : ℕ) : 𝓞 F) - x₀) =
        (n - x₀) + ((c * Ideal.absNorm I : ℕ) : 𝓞 F) := by ring
    rw [e]
    exact I.add_mem hn hmem
  · intro n hn
    have e : n + (((c * Ideal.absNorm I : ℕ) : 𝓞 F) + x₀) - x₀ =
        n + ((c * Ideal.absNorm I : ℕ) : 𝓞 F) := by ring
    rw [e]
    exact I.add_mem hn hmem

theorem tendsto_ratio (e : ℕ) :
    Tendsto (fun j : ℕ => (((j : ℝ) ^ 2) ^ e) / ((((j + 1 : ℕ) : ℝ) ^ 2) ^ e)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun j : ℕ => (j : ℝ) / ((j + 1 : ℕ) : ℝ)) atTop (𝓝 1) := by
    refine (tendsto_natCast_div_add_atTop (1 : ℝ)).congr fun j => ?_
    push_cast
    rfl
  have h2 := (h1.pow 2).pow e
  simp only [one_pow] at h2
  exact h2.congr fun j => by rw [div_pow, div_pow]

private theorem tendsto_scaled_of_interleaved_tendsto (D : ℕ) {u v : ℕ → ℝ} {L : ℝ}
    (hv : Tendsto (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-(D : ℤ)) * v j) atTop (𝓝 L))
    (hup : ∀ᶠ j in atTop, u j ≤ v (j + 1))
    (hlo : ∀ᶠ j in atTop, v j ≤ u (j + 1)) :
    Tendsto (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-(D : ℤ)) * u j) atTop (𝓝 L) := by
  have hg : ∀ j : ℕ, ((j : ℝ) ^ 2) ^ (-(D : ℤ)) = (((j : ℝ) ^ 2) ^ D)⁻¹ := fun j => by
    rw [zpow_neg, zpow_natCast]
  simp only [hg] at hv ⊢
  have hs := tendsto_ratio D
  have hs1 : Tendsto (fun j : ℕ => ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D) /
      ((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D)) atTop (𝓝 1) :=
    hs.comp (tendsto_add_atTop_nat 1)
  have ht : Tendsto (fun j : ℕ => ((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D) /
      ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D)) atTop (𝓝 1) := by
    have h := hs1.inv₀ one_ne_zero
    simpa only [inv_div, inv_one] using h
  have hv2 : Tendsto (fun j : ℕ => ((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ * v (j + 1 + 1))
      atTop (𝓝 L) :=
    (hv.comp (tendsto_add_atTop_nat 1)).comp (tendsto_add_atTop_nat 1)
  have lowT : Tendsto (fun j : ℕ => (((j : ℝ) ^ 2) ^ D) / ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D) *
      ((((j : ℝ) ^ 2) ^ D)⁻¹ * v j)) atTop (𝓝 L) := by
    simpa only [one_mul] using hs.mul hv
  have upT : Tendsto (fun j : ℕ => ((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D) /
      ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D) *
      (((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ * v (j + 1 + 1))) atTop (𝓝 L) := by
    simpa only [one_mul] using ht.mul hv2
  have hup1 : ∀ᶠ j in atTop, u (j + 1) ≤ v (j + 1 + 1) := (tendsto_add_atTop_nat 1).eventually hup
  rw [← tendsto_add_atTop_iff_nat 1]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' lowT upT ?_ ?_
  · filter_upwards [hlo, eventually_ge_atTop 1] with j hj hj1
    have hj0 : ((j : ℝ) ^ 2) ^ D ≠ 0 :=
      pow_ne_zero _ (pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega)))
    have hpos : 0 ≤ ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ := by positivity
    calc (((j : ℝ) ^ 2) ^ D) / ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D) * ((((j : ℝ) ^ 2) ^ D)⁻¹ * v j)
        = ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ * v j := by
          rw [div_mul_eq_mul_div, ← mul_assoc, mul_inv_cancel₀ hj0, one_mul, div_eq_inv_mul]
      _ ≤ ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ * u (j + 1) := mul_le_mul_of_nonneg_left hj hpos
  · filter_upwards [hup1] with j hj
    have hpos : 0 ≤ ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ := by positivity
    have h0 : ((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D) ≠ 0 :=
      pow_ne_zero _ (pow_ne_zero _ (Nat.cast_ne_zero.2 (Nat.succ_ne_zero _)))
    calc ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ * u (j + 1)
        ≤ ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ * v (j + 1 + 1) := mul_le_mul_of_nonneg_left hj hpos
      _ = ((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D) / ((((j + 1 : ℕ) : ℝ) ^ 2) ^ D) *
          (((((j + 1 + 1 : ℕ) : ℝ) ^ 2) ^ D)⁻¹ * v (j + 1 + 1)) := by
          rw [div_mul_eq_mul_div, ← mul_assoc, mul_inv_cancel₀ h0, one_mul, div_eq_inv_mul]

theorem tendsto_sum_coset (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {m : ℕ} (hm : 1 ≤ m)
    {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) (x₀ : 𝓞 F) :
    Tendsto (fun j : ℕ => ((j : ℝ) ^ 2) ^ (-((Formalism.HermitianLatticesTheory.fDeg K * m : ℕ) : ℤ)) *
        ∑ᶠ n ∈ {n : 𝓞 F | n ∈ boxSet K F ((j : ℝ) ^ 2) ∧ n - x₀ ∈ I},
          (Ideal.absNorm (Ideal.span {n}) : ℝ) ^ (m - 1))
      atTop (𝓝 ((m : ℝ) ^ (-(Formalism.HermitianLatticesTheory.fDeg K : ℤ)) /
        Real.sqrt ((2 * Formalism.HermitianLatticesTheory.vInv K) ^ Formalism.HermitianLatticesTheory.fDeg K) / (Ideal.absNorm I : ℝ))) := by
  obtain ⟨y, y', R, hy, hy', hyI, hy'I⟩ := exists_shifts hI x₀
  obtain ⟨j0, hj0⟩ := exists_nat_ge R
  refine tendsto_scaled_of_interleaved_tendsto _ (tendsto_sum_ideal hK hF hm hI) ?_ ?_
  · filter_upwards [eventually_ge_atTop j0] with j hj
    have hRj : R ≤ (j : ℝ) := le_trans hj0 (by exact_mod_cast hj)
    refine sum_le_sum_shift hK hF m (A := {n | n - x₀ ∈ I}) (B := (I : Set (𝓞 F)))
      (T := (j : ℝ) ^ 2) (T' := ((j + 1 : ℕ) : ℝ) ^ 2) y (fun w => (hy w).1) ?_ ?_
    · intro w
      have h1 := (hy w).2
      have h2 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      push_cast
      nlinarith
    · intro n hn
      exact hyI n hn
  · filter_upwards [eventually_ge_atTop j0] with j hj
    have hRj : R ≤ (j : ℝ) := le_trans hj0 (by exact_mod_cast hj)
    refine sum_le_sum_shift hK hF m (A := (I : Set (𝓞 F))) (B := {n | n - x₀ ∈ I})
      (T := (j : ℝ) ^ 2) (T' := ((j + 1 : ℕ) : ℝ) ^ 2) y' (fun w => (hy' w).1) ?_ ?_
    · intro w
      have h1 := (hy' w).2
      have h2 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      push_cast
      nlinarith
    · intro n hn
      exact hy'I n hn

end Formalism.HermitianLattices.Ext.L3.BoxSum
