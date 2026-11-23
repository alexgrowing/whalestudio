import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm

open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Mx n → (H →L[ℂ] H)}

theorem isAvg_sigma {g : Mx n} (hg : g ∈ UJset ε) : IsAvg ε σ (σ g) :=
  ⟨{g}, 1, isCompact_singleton, Set.singleton_subset_iff.2 hg, zero_le_one, fun ι _ x w M _ h => by
    rw [one_mul]; exact h g rfl⟩

theorem IsAvg.add {T T' : H → H} (h : IsAvg ε σ T) (h' : IsAvg ε σ T') : IsAvg ε σ (fun w => T w + T' w) := by
  obtain ⟨Z, C, h1, h2, h3, h4⟩ := h
  obtain ⟨Z', C', k1, k2, k3, k4⟩ := h'
  refine ⟨Z ∪ Z', C + C', h1.union k1, Set.union_subset h2 k2, add_nonneg h3 k3, fun ι _ x w M hM hb => ?_⟩
  simp only [inner_add_right, Finset.sum_add_distrib, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (h4 ι x w M hM fun y hy => hb y (Or.inl hy))
    (k4 ι x w M hM fun y hy => hb y (Or.inr hy)))

theorem IsAvg.comp (hσ : IsURepOn (UJset ε) σ) {T T' : H → H} (h : IsAvg ε σ T) (h' : IsAvg ε σ T') :
    IsAvg ε σ (fun w => T (T' w)) := by
  obtain ⟨Z, C, h1, h2, h3, h4⟩ := h
  obtain ⟨Z', C', k1, k2, k3, k4⟩ := h'
  refine ⟨(fun p : Mx n × Mx n => p.1 * p.2) '' (Z ×ˢ Z'), C * C',
    (h1.prod k1).image (continuous_fst.matrix_mul continuous_snd), ?_, mul_nonneg h3 k3, fun ι _ x w M hM hb => ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact mul_mem_UJ (h2 hp.1) (k2 hp.2)
  rw [mul_assoc]
  refine h4 ι x (fun j => T' (w j)) (C' * M) (mul_nonneg k3 hM) fun y hy => ?_
  simp only [inner_sigma hσ (h2 hy)]
  refine k4 ι (fun j => σ y⁻¹ (x j)) w M hM fun y' hy' => ?_
  have := hb (y * y') ⟨(y, y'), ⟨hy, hy'⟩, rfl⟩
  simpa only [sigma_mul hσ (h2 hy) (k2 hy'), inner_sigma hσ (h2 hy)] using this

theorem IsAvg.smul (c : ℂ) {T : H → H} (h : IsAvg ε σ T) : IsAvg ε σ (fun w => c • T w) := by
  obtain ⟨Z, C, h1, h2, h3, h4⟩ := h
  refine ⟨Z, ‖c‖ * C, h1, h2, mul_nonneg (norm_nonneg _) h3, fun ι _ x w M hM hb => ?_⟩
  simp only [inner_smul_right, ← Finset.mul_sum, norm_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h4 ι x w M hM hb) (norm_nonneg _)

theorem isAvg_zero : IsAvg ε σ (fun _ => 0) :=
  ⟨∅, 0, isCompact_empty, Set.empty_subset _, le_rfl, fun ι _ x w M _ _ => by simp⟩

theorem isAvg_kAvg [CompleteSpace H] (hσ : IsURepOn (UJset ε) σ) {e : KG ε → ℂ} (he : Continuous e) :
    IsAvg ε σ (kAvg ε σ e) := by
  refine ⟨Kset ε, ∫ k, ‖e k‖ ∂(muK ε), (maximal_compact_facts n ε).2.1, fun k hk => K_le_UJ hk,
    integral_nonneg fun _ => norm_nonneg _, fun ι _ x w M hM hb => ?_⟩
  have hi : ∀ v : H, Integrable (fun k : KG ε => e k • σ (toMK k) v) (muK ε) := fun v =>
    (he.smul ((hσ.2.2 v).comp_continuous (continuous_toMK ε)
      fun k => K_le_UJ (toMK_mem_K k))).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp only [kAvg]
  simp only [fun j => (integral_inner (𝕜 := ℂ) (hi (w j)) (x j)).symm]
  rw [← integral_finset_sum _ fun j _ => (hi (w j)).const_inner (x j), ← integral_mul_const]
  refine norm_integral_le_of_norm_le ((he.norm.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)).mul_const M) (Eventually.of_forall fun k => ?_)
  simp only [inner_smul_right, ← Finset.mul_sum, norm_mul]
  exact mul_le_mul_of_nonneg_left (hb _ (toMK_mem_K k)) (norm_nonneg _)

theorem isAvg_closure : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → (∀ g ∈ UJset ε, IsAvg ε σ (σ g)) ∧ (∀ T T' : H → H, IsAvg ε σ T → IsAvg ε σ T' → IsAvg ε σ (fun w => T w + T' w) ∧ IsAvg ε σ (fun w => T (T' w))) ∧ (∀ (c : ℂ) (T : H → H), IsAvg ε σ T → IsAvg ε σ (fun w => c • T w)) ∧ (∀ e : KG ε → ℂ, Continuous e → IsAvg ε σ (kAvg ε σ e)) ∧ IsAvg ε σ (fun _ => 0) :=
  fun _ _ _ _ _ _ _ hσ => ⟨fun _ hg => isAvg_sigma hg, fun _ _ h h' => ⟨h.add h', h.comp hσ h'⟩,
    fun c _ h => h.smul c, fun _ he => isAvg_kAvg hσ he, isAvg_zero⟩

end GlobalTheory.TypeSum
