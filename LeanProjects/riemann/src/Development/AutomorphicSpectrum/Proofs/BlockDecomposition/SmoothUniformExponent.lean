import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''

namespace GlobalTheory.CompanionTheory.SmoothUniform

theorem smooth_uniform_exponent : ∀ {R : Type} [CommRing R] (l : ℕ) [Fact l.Prime] (k : ℕ) {M : Type w} [AddCommGroup M] [Module R M] (ρ : Multiplicative (Fin k → ℤ_[l]) →* (M →ₗ[R] M)) (n : ℕ), (∀ x : M, ∃ a : ℕ, ∀ g : Fin k → ℤ_[l], ρ (Multiplicative.ofAdd ((l : ℤ_[l]) ^ a • g)) x = x) → ∀ f : LocallyConstant (Fin (n + 1) → Fin k → ℤ_[l]) M, ∃ a : ℕ, ∀ (g : Fin k → ℤ_[l]) (x : Fin (n + 1) → Fin k → ℤ_[l]), f (fun i => (l : ℤ_[l]) ^ a • g + x i) = f x ∧ ρ (Multiplicative.ofAdd ((l : ℤ_[l]) ^ a • g)) (f x) = f x := by
  intro R _ l _ k M _ _ ρ n hsm f
  have hl : (1 : ℝ) < (l : ℝ) := by
    exact_mod_cast (Fact.out : l.Prime).one_lt
  have hfin : (Set.range f).Finite := f.range_finite
  choose A hA using hsm
  obtain ⟨a₁, ha₁⟩ : ∃ a₁ : ℕ, ∀ m ∈ Set.range f, A m ≤ a₁ := by
    obtain ⟨b, hb⟩ := (hfin.image A).bddAbove
    exact ⟨b, fun m hm => hb (Set.mem_image_of_mem A hm)⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric
    (s := (Set.univ : Set (Fin (n + 1) → Fin k → ℤ_[l])))
    (c := fun m : M => f ⁻¹' {m}) isCompact_univ
    (fun m => f.isLocallyConstant.isOpen_fiber m)
    (fun x _ => Set.mem_iUnion.2 ⟨f x, rfl⟩)
  obtain ⟨a₂, ha₂⟩ : ∃ a₂ : ℕ, (1 / (l : ℝ)) ^ a₂ < δ :=
    exists_pow_lt_of_lt_one hδ (by
      rw [div_lt_one (by linarith)]
      exact hl)
  refine ⟨max a₁ a₂, fun g x => ⟨?_, ?_⟩⟩
  · have hnorm : ‖(l : ℤ_[l]) ^ (max a₁ a₂) • g‖ < δ := by
      have hle : ‖(l : ℤ_[l]) ^ (max a₁ a₂) • g‖ ≤ (1 / (l : ℝ)) ^ a₂ := by
        refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
        have h1 : ‖(l : ℤ_[l]) ^ (max a₁ a₂)‖ = (1 / (l : ℝ)) ^ (max a₁ a₂) := by
          rw [PadicInt.norm_p_pow, zpow_neg, zpow_natCast, one_div, inv_pow]
        have h2 : (1 / (l : ℝ)) ^ (max a₁ a₂) ≤ (1 / (l : ℝ)) ^ a₂ :=
          pow_le_pow_of_le_one (by positivity)
            (by rw [div_le_one (by linarith)]; exact hl.le) (le_max_right _ _)
        calc ‖((l : ℤ_[l]) ^ (max a₁ a₂) • g) j‖
            = ‖(l : ℤ_[l]) ^ (max a₁ a₂)‖ * ‖g j‖ := by
              simp [Pi.smul_apply, norm_mul]
          _ ≤ ‖(l : ℤ_[l]) ^ (max a₁ a₂)‖ * 1 :=
              mul_le_mul_of_nonneg_left (PadicInt.norm_le_one _) (norm_nonneg _)
          _ ≤ (1 / (l : ℝ)) ^ a₂ := by rw [mul_one, h1]; exact h2
      exact hle.trans_lt ha₂
    obtain ⟨m, hm⟩ := hball x (Set.mem_univ x)
    have hx : f x = m := hm (Metric.mem_ball_self hδ)
    have hy : f (fun i => (l : ℤ_[l]) ^ (max a₁ a₂) • g + x i) = m := by
      apply hm
      rw [Metric.mem_ball, dist_eq_norm]
      refine lt_of_le_of_lt ?_ hnorm
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
      simp
    rw [hx, hy]
  · have hle : A (f x) ≤ max a₁ a₂ := (ha₁ _ ⟨x, rfl⟩).trans (le_max_left _ _)
    have hsplit : (l : ℤ_[l]) ^ (max a₁ a₂) • g
        = (l : ℤ_[l]) ^ (A (f x)) • ((l : ℤ_[l]) ^ (max a₁ a₂ - A (f x)) • g) := by
      rw [smul_smul, ← pow_add, Nat.add_sub_cancel' hle]
    rw [hsplit]
    exact hA (f x) _

end GlobalTheory.CompanionTheory.SmoothUniform
