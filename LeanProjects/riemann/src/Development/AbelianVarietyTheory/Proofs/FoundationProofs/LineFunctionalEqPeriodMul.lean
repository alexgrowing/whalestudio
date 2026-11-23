import Mathlib
import GroundTheory.PAdicHodge.AxLemma

open TensorProduct GroundTheory.PAdicHodge UniformSpace

namespace GlobalTheory

theorem line_functional_eq_period_mul : ∀ (l : ℕ) [Fact l.Prime] (M S : Type) [AddCommGroup M] [Module ℤ_[l] M] (B : Submodule ℤ_[l] M)
  (g : S → Module.End ℤ_[l] M) (ρ : S → Matrix (Fin 2) (Fin 2) (PadicAlgCl l))
  (L : TensorProduct ℤ_[l] (PadicAlgCl l) M →ₗ[PadicAlgCl l] ℂ_[l]) (F : Finset (PadicAlgCl l)),
  (∀ K : IntermediateField ℚ_[l] (PadicAlgCl l), (∀ a ∈ F, a ∈ K) → ∀ τ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l,
    ∃ s, ∀ b ∈ B, L (1 ⊗ₜ[ℤ_[l]] g s b) = τ • L (1 ⊗ₜ[ℤ_[l]] b)) →
  ∀ (m : ℕ) (σ : Fin m → (Fin 2 → PadicAlgCl l) →ₗ[PadicAlgCl l] TensorProduct ℤ_[l] (PadicAlgCl l) M),
  (∀ i v, σ i v ∈ LinearMap.range (LinearMap.baseChange (PadicAlgCl l) B.subtype)) →
  (∀ i s v, LinearMap.baseChange (PadicAlgCl l) (g s) (σ i v) = σ i (Matrix.mulVec (ρ s) v)) →
  (∀ i, L (σ i ![1, 0]) = 0) →
  ∃ (κ : Fin m → PadicAlgCl l) (per : ℂ_[l]), ‖per‖ = 1 ∧ ∀ i v, L (σ i v) = per * ((κ i * v 1 : PadicAlgCl l) : ℂ_[l]) := by
  intro l _ M S _ _ B g ρ L F hgal m σ hσB hσeq hσ0
  classical

  have hsm : ∀ (a : PadicAlgCl l) (z : ℂ_[l]), a • z = (a : ℂ_[l]) * z := fun a z => by
    rw [Algebra.smul_def]; rfl
  set y : Fin m → ℂ_[l] := fun i => L (σ i ![0, 1]) with hy
  have hLv : ∀ i v, L (σ i v) = (v 1 : ℂ_[l]) * y i := by
    intro i v
    have hv : v = v 0 • ![1, 0] + v 1 • ![0, 1] := by
      ext j; fin_cases j <;> simp
    calc L (σ i v) = L (σ i (v 0 • ![1, 0] + v 1 • ![0, 1])) := by rw [← hv]
      _ = _ := by rw [map_add, map_smul, map_smul, map_add, map_smul, map_smul, hσ0, smul_zero,
          zero_add, hsm]
  by_cases hall : ∀ i, y i = 0
  · refine ⟨0, 1, norm_one, fun i v => ?_⟩
    rw [hLv, hall i]; simp
  push_neg at hall
  obtain ⟨i₀, hy0⟩ := hall

  have hex : ∀ i, ∃ Sf : Finset (PadicAlgCl l × B),
      σ i ![0, 1] = ∑ q ∈ Sf, q.1 ⊗ₜ[ℤ_[l]] (q.2 : M) := by
    intro i
    obtain ⟨t, ht⟩ := hσB i ![0, 1]
    obtain ⟨Sf, rfl⟩ := TensorProduct.exists_finset t
    refine ⟨Sf, ?_⟩
    rw [← ht, map_sum]
    simp [LinearMap.baseChange_tmul]
  choose Sf hSf using hex
  set T : Finset (PadicAlgCl l) := F ∪ Finset.univ.biUnion (fun i => (Sf i).image Prod.fst) with hT
  set K : IntermediateField ℚ_[l] (PadicAlgCl l) := IntermediateField.adjoin ℚ_[l] (T : Set (PadicAlgCl l))
    with hK
  haveI : FiniteDimensional ℚ_[l] K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hTK : ∀ a ∈ T, a ∈ K := fun a ha => IntermediateField.subset_adjoin _ _ (by simpa using ha)
  have hFK : ∀ a ∈ F, a ∈ K := fun a ha => hTK a (Finset.mem_union_left _ ha)
  have hSK : ∀ i, ∀ q ∈ Sf i, q.1 ∈ K := fun i q hq =>
    hTK _ (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _,
      Finset.mem_image_of_mem _ hq⟩))

  have hmul : ∀ τ : PadicAlgCl l ≃ₐ[K] PadicAlgCl l, ∃ c : PadicAlgCl l,
      ∀ i, τ • y i = (c : ℂ_[l]) * y i := by
    intro τ
    obtain ⟨s, hs⟩ := hgal K hFK τ
    refine ⟨ρ s 1 1, fun i => ?_⟩
    have h1 : L (LinearMap.baseChange (PadicAlgCl l) (g s) (σ i ![0, 1])) = τ • y i := by
      rw [hy]
      simp only
      rw [hSf i, map_sum, map_sum, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [LinearMap.baseChange_tmul]
      have e1 : ∀ x : M, q.1 ⊗ₜ[ℤ_[l]] x = q.1 • ((1 : PadicAlgCl l) ⊗ₜ[ℤ_[l]] x) := fun x => by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e1, e1 (q.2 : M), map_smul, map_smul, hsm, hsm, hs _ q.2.2, smul_mul',
        gal_smul_coe, show τ q.1 = q.1 from τ.commutes ⟨q.1, hSK i q hq⟩]
    rw [← h1, hσeq, hLv]
    congr 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hfix : ∀ i, ∃ k : K, ((k : PadicAlgCl l) : ℂ_[l]) = y i / y i₀ := by
    intro i
    refine exists_eq_coe_of_forall_smul_eq fun τ => ?_
    obtain ⟨c, hc⟩ := hmul τ
    have hne : τ • y i₀ ≠ 0 := by
      rw [← norm_ne_zero_iff, norm_smul_gal, norm_ne_zero_iff]; exact hy0
    have hc0 : (c : ℂ_[l]) ≠ 0 := by
      intro h0; apply hne; rw [hc, h0, zero_mul]
    rw [smul_div₀', hc, hc]
    field_simp
  choose k hk using hfix

  obtain ⟨a, ha⟩ := (Completion.denseRange_coe (α := PadicAlgCl l)).exists_dist_lt (y i₀)
    (norm_pos_iff.2 hy0)
  rw [dist_eq_norm] at ha
  have hna : ‖(a : ℂ_[l])‖ = ‖y i₀‖ := by
    have e : (a : ℂ_[l]) = -(y i₀ - (a : ℂ_[l])) + y i₀ := by ring
    rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg]; exact ha.ne),
      norm_neg, max_eq_right ha.le]
  have ha0 : (a : ℂ_[l]) ≠ 0 := by
    rw [← norm_ne_zero_iff, hna, norm_ne_zero_iff]; exact hy0
  refine ⟨fun i => (k i : PadicAlgCl l) * a, y i₀ / (a : ℂ_[l]), ?_, fun i v => ?_⟩
  · rw [norm_div, hna, div_self (norm_ne_zero_iff.2 hy0)]
  · rw [hLv, Completion.coe_mul, Completion.coe_mul, hk i]
    field_simp

end GlobalTheory
