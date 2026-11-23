import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsResidueIdempotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentLiftAdicCompleteFreeAlgebraStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AzumayaAlgEquivMatrixOfIdempotentStatement
open IsLocalRing
open scoped TensorProduct

namespace GlobalTheory.AzumayaLocal

theorem mem_left {A Λ : Type} [CommRing A] [Ring Λ] [Algebra A Λ] {I : Ideal A} (w : Λ) {z : Λ}
    (hz : z ∈ I • (⊤ : Submodule A Λ)) : w * z ∈ I • (⊤ : Submodule A Λ) := by
  refine Submodule.smul_induction_on hz (fun a ha t _ => ?_) (fun x y hx hy => ?_)
  · rw [mul_smul_comm]; exact Submodule.smul_mem_smul ha trivial
  · rw [mul_add]; exact Submodule.add_mem _ hx hy

theorem mem_right {A Λ : Type} [CommRing A] [Ring Λ] [Algebra A Λ] {I : Ideal A} (w : Λ) {z : Λ}
    (hz : z ∈ I • (⊤ : Submodule A Λ)) : z * w ∈ I • (⊤ : Submodule A Λ) := by
  refine Submodule.smul_induction_on hz (fun a ha t _ => ?_) (fun x y hx hy => ?_)
  · rw [smul_mul_assoc]; exact Submodule.smul_mem_smul ha trivial
  · rw [add_mul]; exact Submodule.add_mem _ hx hy

end GlobalTheory.AzumayaLocal

theorem GlobalTheory.AzumayaLocal.finite_residueField : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [IsLocalRing A] [Algebra ℤ_[ℓ] A] [Module.Finite ℤ_[ℓ] A], Finite (IsLocalRing.ResidueField A) := by
  intro ℓ _ A _ _ _ _
  have hmax : (maximalIdeal A).comap (algebraMap ℤ_[ℓ] A) = maximalIdeal ℤ_[ℓ] :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal A))
  haveI : IsLocalHom (algebraMap ℤ_[ℓ] A) := ⟨fun x hx => by
    by_contra h
    have : x ∈ (maximalIdeal A).comap (algebraMap ℤ_[ℓ] A) := by rw [hmax]; exact h
    exact (mem_maximalIdeal _).1 this hx⟩
  have : Finite (IsLocalRing.ResidueField ℤ_[ℓ]) := Finite.of_equiv _ (PadicInt.residueField).symm.toEquiv
  exact Module.finite_of_finite (IsLocalRing.ResidueField ℤ_[ℓ])

theorem GlobalTheory.AzumayaLocal.exists_right_inverse : ∀ (A : Type) [CommRing A] [IsLocalRing A] (Λ : Type) [Ring Λ] [Algebra A Λ] [Module.Finite A Λ] (u : Λ), u - 1 ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A Λ) → ∃ v : Λ, u * v = 1 := by
  intro A _ _ Λ _ _ _ u hu
  let f : Λ →ₗ[A] Λ := LinearMap.mulLeft A u
  have hle : (⊤ : Submodule A Λ) ≤ LinearMap.range f ⊔ (maximalIdeal A) • (⊤ : Submodule A Λ) := by
    intro y _
    have hy : y = u * y - (u - 1) * y := by noncomm_ring
    rw [hy]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left ⟨y, rfl⟩)
      (Submodule.mem_sup_right (GlobalTheory.AzumayaLocal.mem_right y hu))
  have htop : LinearMap.range f = ⊤ :=
    top_le_iff.1 (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
      (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge hle)
  obtain ⟨v, hv⟩ := LinearMap.range_eq_top.1 htop 1
  exact ⟨v, hv⟩

theorem GlobalTheory.AzumayaLocal.corner_eq_smul : ∀ (A : Type) [CommRing A] [IsLocalRing A] (Λ : Type) [Ring Λ] [Algebra A Λ] [Module.Finite A Λ] (e : Λ), IsIdempotentElem e → (∀ y : Λ, ∃ c : A, e * y * e - c • e ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A Λ)) → ∀ y : Λ, ∃ c : A, e * y * e = c • e := by
  intro A _ _ Λ _ _ _ e he h y
  let g : Λ →ₗ[A] Λ := (LinearMap.mulRight A e).comp (LinearMap.mulLeft A e)
  have hg : ∀ z, g z = e * z * e := fun z => rfl
  have hge : g e = e := by rw [hg, he.eq, he.eq]
  have hgg : ∀ z, g (e * z * e) = e * z * e := by
    intro z
    rw [hg, ← mul_assoc, ← mul_assoc, he.eq, mul_assoc (e * z) e e, he.eq]
  have hS : LinearMap.range g ≤ A ∙ e := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (by rw [LinearMap.range_eq_map]; exact Module.Finite.fg_top.map g)
      (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge ?_
    rintro _ ⟨z, rfl⟩
    obtain ⟨c, hc⟩ := h z
    have key : g z - c • e = g (e * z * e - c • e) := by
      rw [map_sub, map_smul, hgg, hge, hg]
    have hmem : g z - c • e ∈ (maximalIdeal A) • LinearMap.range g := by
      rw [key, LinearMap.range_eq_map, ← Submodule.map_smul'']
      exact Submodule.mem_map_of_mem hc
    rw [show g z = c • e + (g z - c • e) by abel]
    exact Submodule.add_mem_sup (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self e)) hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (hS ⟨y, rfl⟩)
  exact ⟨c, hc.symm⟩

namespace GlobalTheory.AzumayaLocal

theorem azumaya_local_matrix : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (A : Type) [CommRing A] [IsLocalRing A] [Algebra ℤ_[ℓ] A]
    [Module.Finite ℤ_[ℓ] A] (Λ : Type) [Ring Λ] [Algebra A Λ] [IsAzumaya A Λ] [Module.Free A Λ]
    (n : ℕ), Module.finrank A Λ = n ^ 2 → Nonempty (Λ ≃ₐ[A] Matrix (Fin n) (Fin n) A) := by
  intro ℓ _ A _ _ _ _ Λ _ _ _ _ n hn
  haveI : IsAdicComplete (maximalIdeal A) A :=
    GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[ℓ] A
  haveI : Finite (ResidueField A) := GlobalTheory.AzumayaLocal.finite_residueField ℓ A
  haveI : Nontrivial Λ := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact zero_ne_one (FaithfulSMul.algebraMap_injective A Λ
      (Subsingleton.elim (algebraMap A Λ 0) (algebraMap A Λ 1)))
  set M := (maximalIdeal A) • (⊤ : Submodule A Λ) with hM
  obtain ⟨x, h1, h2, N, a, b, h3⟩ := GlobalTheory.T.exists_residue_idempotent' A Λ
  obtain ⟨e, he, hex⟩ := GlobalTheory.T.exists_idempotent_lift_adicComplete_free_algebra A (maximalIdeal A) Λ x h1
  have hcorner : ∀ y : Λ, ∃ c : A, e * y * e - c • e ∈ M := by
    intro y
    obtain ⟨c, hc⟩ := h2 y
    refine ⟨c, ?_⟩
    have : e * y * e - c • e = (x * y * x - c • x) + ((e - x) * (y * e) + x * y * (e - x) - c • (e - x)) := by
      simp only [sub_mul, mul_sub, smul_sub, mul_assoc]; abel
    rw [this]
    exact M.add_mem hc (M.sub_mem (M.add_mem (mem_right _ hex) (mem_left _ hex)) (M.smul_mem c hex))
  have hu : ∑ i, a i * e * b i - 1 ∈ M := by
    have : ∑ i, a i * e * b i - 1 = (∑ i, a i * x * b i - 1) + ∑ i, a i * (e - x) * b i := by
      simp only [mul_sub, sub_mul, Finset.sum_sub_distrib]; abel
    rw [this]
    exact M.add_mem h3 (M.sum_mem fun i _ => mem_right _ (mem_left _ hex))
  obtain ⟨v, hv⟩ := GlobalTheory.AzumayaLocal.exists_right_inverse A Λ _ hu
  exact GlobalTheory.T.nonempty_algEquiv_matrix_of_isAzumaya_of_full_idempotent A Λ n hn e he (GlobalTheory.AzumayaLocal.corner_eq_smul A Λ e he hcorner) ⟨N, a, fun i => b i * v, by
    rw [← hv, Finset.sum_mul]; simp only [mul_assoc]⟩

end GlobalTheory.AzumayaLocal
