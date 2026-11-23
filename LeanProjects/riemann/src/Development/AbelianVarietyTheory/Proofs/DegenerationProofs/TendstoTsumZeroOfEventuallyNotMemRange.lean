import Mathlib

open Module Filter Topology

namespace GlobalTheory

theorem eq_zero_of_forall_pow_nsmul {X : Type} [AddCommGroup X] [Module.Free ℤ X] {n : ℕ}
    (hn : 2 ≤ n) {x : X} (hx : ∀ j : ℕ, ∃ μ : X, x = n ^ j • μ) : x = 0 := by
  let b := Module.Free.chooseBasis ℤ X
  apply b.repr.injective
  ext i
  rw [map_zero, Finsupp.zero_apply]
  obtain ⟨μ, hμ⟩ := hx (b.repr x i).natAbs
  have hd : ((n : ℤ) ^ (b.repr x i).natAbs) ∣ b.repr x i := by
    refine ⟨b.repr μ i, ?_⟩
    conv_lhs => rw [hμ]
    simp [map_nsmul]
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd
  rw [Int.natAbs_pow, Int.natAbs_natCast]
  exact Nat.lt_pow_self (by omega)

theorem tendsto_tsum_zero_of_eventually_notMem_range {K X Y : Type} [NontriviallyNormedField K]
    [IsUltrametricDist K] (τ : X → K) (hτ : Tendsto τ cofinite (𝓝 0)) (f : ℕ → Y → X)
    (hf : ∀ z, τ z ≠ 0 → ∀ᶠ j in atTop, ∀ μ, f j μ ≠ z) :
    Tendsto (fun j => ∑' μ, τ (f j μ)) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hS : {z | ¬ ‖τ z‖ < ε / 2}.Finite := by
    have := hτ (Metric.ball_mem_nhds (0 : K) (half_pos hε))
    rw [Filter.mem_map, Filter.mem_cofinite] at this
    convert this using 1
    ext z
    simp
  have hev : ∀ᶠ j in atTop, ∀ z ∈ {z | ¬ ‖τ z‖ < ε / 2}, ∀ μ, f j μ ≠ z :=
    (hS.eventually_all).2 fun z hz => hf z (fun h0 => hz (by rw [h0, norm_zero]; exact half_pos hε))
  filter_upwards [hev] with j hj
  rw [dist_zero_right]
  refine lt_of_le_of_lt
    (IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (half_pos hε).le fun μ => ?_) (half_lt_self hε)
  by_contra h
  exact hj (f j μ) (show ¬ ‖τ (f j μ)‖ < ε / 2 from fun h' => h h'.le) μ rfl

theorem mem_class_of_le {X : Type} [AddCommGroup X] {n : ℕ} {α : ℕ → X}
    (hα : ∀ j, ∃ μ, α (j + 1) = α j + n ^ j • μ) {z : X} {j k : ℕ} (hjk : j ≤ k)
    (hz : ∃ μ, z = α k + n ^ k • μ) : ∃ μ, z = α j + n ^ j • μ := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hjk
  clear hjk
  induction d generalizing z with
  | zero => simpa using hz
  | succ d ih =>
    obtain ⟨μ, rfl⟩ := hz
    obtain ⟨ν, hν⟩ := hα (j + d)
    apply ih
    refine ⟨ν + n • μ, ?_⟩
    rw [← add_assoc, hν, pow_succ, mul_smul, smul_add]
    abel

theorem tendsto_tsum_pow_classes :
    ∀ (K X : Type) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
      [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (n : ℕ), 2 ≤ n →
      ∀ (σ : X → K), Filter.Tendsto σ Filter.cofinite (nhds 0) → ∀ α : ℕ → X,
      (∀ j, ∃ μ, α (j + 1) = α j + n ^ j • μ) →
      (∀ χ : X, (∀ j, ∃ μ, χ = α j + n ^ j • μ) →
        Filter.Tendsto (fun j => ∑' μ, σ (α j + n ^ j • μ)) Filter.atTop (nhds (σ χ))) ∧
      ((¬ ∃ χ : X, ∀ j, ∃ μ, χ = α j + n ^ j • μ) →
        Filter.Tendsto (fun j => ∑' μ, σ (α j + n ^ j • μ)) Filter.atTop (nhds 0)) := by
  classical
  intro K X _ _ _ _ _ _ n hn σ hσ α hα
  have hinj : ∀ j, Function.Injective (fun μ : X => α j + n ^ j • μ) := by
    intro j μ ν h
    simp only [add_right_inj] at h
    have hne : ((n ^ j : ℕ) : ℤ) ≠ 0 := by exact_mod_cast pow_ne_zero j (by omega : n ≠ 0)
    have h' : ((n ^ j : ℕ) : ℤ) • μ = ((n ^ j : ℕ) : ℤ) • ν := by
      rw [natCast_zsmul, natCast_zsmul]
      exact h
    exact smul_right_injective X hne h'
  have hsum : ∀ τ : X → K, Tendsto τ cofinite (𝓝 0) → ∀ j, Summable (fun μ => τ (α j + n ^ j • μ)) :=
    fun τ hτ j => NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero (hτ.comp (hinj j).tendsto_cofinite)
  have hfar : ∀ z w : X, z ≠ w → ∀ᶠ j in atTop, ¬ ∃ μ, z = w + n ^ j • μ := by
    intro z w hzw
    by_contra h
    rw [Filter.not_eventually] at h
    simp only [not_not] at h
    apply hzw
    have h0 : z - w = 0 := by
      refine eq_zero_of_forall_pow_nsmul hn (fun j => ?_)
      obtain ⟨i, ⟨μ, hμ⟩, hji⟩ := (h.and_eventually (eventually_ge_atTop j)).exists
      refine ⟨n ^ (i - j) • μ, ?_⟩
      rw [hμ, add_sub_cancel_left, ← mul_smul, ← pow_add, Nat.add_sub_cancel' hji]
    exact sub_eq_zero.mp h0
  constructor
  · intro χ hχ
    let τ := Function.update σ χ 0
    have hτ : Tendsto τ cofinite (𝓝 0) := by
      apply hσ.congr'
      filter_upwards [(Set.finite_singleton χ).compl_mem_cofinite] with z hz
      simp [τ, Set.mem_compl_singleton_iff.mp hz]
    have h2 := tendsto_tsum_zero_of_eventually_notMem_range τ hτ (fun j μ => α j + n ^ j • μ) (by
      intro z hz
      have hzχ : z ≠ χ := by
        rintro rfl
        simp [τ] at hz
      filter_upwards [hfar z χ hzχ] with j hj μ hμ
      apply hj
      obtain ⟨ν, hν⟩ := hχ j
      have hμ' : z = α j + n ^ j • μ := hμ.symm
      refine ⟨μ - ν, ?_⟩
      rw [hμ', hν, smul_sub]
      abel)
    have heq : ∀ j, ∑' μ, σ (α j + n ^ j • μ) = σ χ + ∑' μ, τ (α j + n ^ j • μ) := by
      intro j
      obtain ⟨μj, hμj⟩ := hχ j
      rw [(hsum σ hσ j).tsum_eq_add_tsum_ite μj]
      congr 1
      · rw [hμj]
      · refine tsum_congr fun μ => ?_
        by_cases h : μ = μj
        · subst h
          simp [τ, ← hμj]
        · have hne : α j + n ^ j • μ ≠ χ := fun h' => h (hinj j (h'.trans hμj))
          simp [τ, h, hne]
    have h3 := tendsto_const_nhds (x := σ χ) |>.add h2
    rw [add_zero] at h3
    exact h3.congr (fun j => (heq j).symm)
  · intro hno
    apply tendsto_tsum_zero_of_eventually_notMem_range σ hσ (fun j μ => α j + n ^ j • μ)
    intro z _
    obtain ⟨j0, hj0⟩ : ∃ j0, ¬ ∃ μ, z = α j0 + n ^ j0 • μ := by
      by_contra h
      exact hno ⟨z, fun j => by
        by_contra h'
        exact h ⟨j, h'⟩⟩
    filter_upwards [eventually_ge_atTop j0] with j hj μ hμ
    exact hj0 (mem_class_of_le hα hj ⟨μ, hμ.symm⟩)

end GlobalTheory
