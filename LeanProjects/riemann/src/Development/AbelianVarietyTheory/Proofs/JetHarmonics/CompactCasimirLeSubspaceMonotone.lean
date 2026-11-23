import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CasKIsSymmetricAndFormStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ReInnerLeOnImageOfIntertwiningStatement
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem casK_mem_of_compact_stable {M : Type} [AddCommGroup M] [Module ℂ M] {n : ℕ} (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ M) (S : Submodule ℂ M)
    (hS : ∀ a b, ε a = ε b → ∀ x ∈ S, E a b x ∈ S) : ∀ x ∈ S, CasK ε E x ∈ S := by
  intro x hx
  unfold CasK
  simp only [LinearMap.sum_apply]
  refine S.sum_mem fun a _ => S.sum_mem fun b _ => ?_
  split_ifs with h
  · exact hS _ _ h _ (hS _ _ h.symm _ hx)
  · simp

theorem quadForm_le_on_sup {M : Type} [NormedAddCommGroup M] [InnerProductSpace ℂ M] (B : M →ₗ[ℂ] M)
    (hB : B.IsSymmetric) (C : ℝ) (S₁ S₂ : Submodule ℂ M) [FiniteDimensional ℂ S₁] [FiniteDimensional ℂ S₂]
    (h₁ : ∀ x ∈ S₁, B x ∈ S₁) (h₂ : ∀ x ∈ S₂, B x ∈ S₂)
    (b₁ : ∀ x ∈ S₁, (⟪x, B x⟫_ℂ).re ≤ C * ‖x‖ ^ 2) (b₂ : ∀ x ∈ S₂, (⟪x, B x⟫_ℂ).re ≤ C * ‖x‖ ^ 2) :
    ∀ x ∈ S₁ ⊔ S₂, (⟪x, B x⟫_ℂ).re ≤ C * ‖x‖ ^ 2 := by
  let e := WithLp.linearEquiv 2 ℂ (S₁ × S₂)
  let Φ : WithLp 2 (S₁ × S₂) →ₗ[ℂ] M := (S₁.subtype.coprod S₂.subtype) ∘ₗ e.toLinearMap
  let A : WithLp 2 (S₁ × S₂) →ₗ[ℂ] WithLp 2 (S₁ × S₂) :=
    e.symm.toLinearMap ∘ₗ ((B.restrict h₁).prodMap (B.restrict h₂)) ∘ₗ e.toLinearMap
  have hA1 : ∀ z, ((A z).fst : M) = B z.fst := fun z => rfl
  have hA2 : ∀ z, ((A z).snd : M) = B z.snd := fun z => rfl
  have hΦ : ∀ z, Φ z = (z.fst : M) + (z.snd : M) := fun z => rfl
  have key := GlobalTheory.T.re_inner_le_on_image_of_intertwining' (WithLp 2 (S₁ × S₂)) M Φ A B C
    (by
      intro z w
      simp only [WithLp.prod_inner_apply, Submodule.coe_inner]
      change ⟪((A z).fst : M), (w.fst : M)⟫_ℂ + ⟪((A z).snd : M), (w.snd : M)⟫_ℂ =
        ⟪(z.fst : M), ((A w).fst : M)⟫_ℂ + ⟪(z.snd : M), ((A w).snd : M)⟫_ℂ
      rw [hA1, hA2, hA1, hA2, hB, hB])
    hB
    (by
      intro z
      rw [hΦ, hΦ, hA1, hA2, map_add])
    (by
      intro z
      rw [WithLp.prod_norm_sq_eq_of_L2]
      simp only [WithLp.prod_inner_apply, Submodule.coe_inner]
      change (⟪(z.fst : M), ((A z).fst : M)⟫_ℂ + ⟪(z.snd : M), ((A z).snd : M)⟫_ℂ).re ≤
        C * (‖(z.fst : M)‖ ^ 2 + ‖(z.snd : M)‖ ^ 2)
      rw [hA1, hA2, Complex.add_re, mul_add]
      exact add_le_add (b₁ _ z.fst.2) (b₂ _ z.snd.2))
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  exact key (WithLp.toLp 2 (⟨y, hy⟩, ⟨z, hz⟩))

theorem casKLe_subspace_mono : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M), KUnit ε E → (∀ c, CasKLe ε E c 0) ∧ (∀ c x y, CasKLe ε E c x → CasKLe ε E c y → CasKLe ε E c (x + y)) ∧ (∀ c (a : ℂ) x, CasKLe ε E c x → CasKLe ε E c (a • x)) ∧ ∀ c c' x, 0 ≤ c → c ≤ c' → CasKLe ε E c x → CasKLe ε E c' x := by
  intro M _ _ n ε E hU
  refine ⟨fun c => ⟨⊥, inferInstance, ?_, Submodule.zero_mem _, ?_⟩, ?_, ?_, ?_⟩
  · intro a b _ x hx
    rw [Submodule.mem_bot] at hx
    simp [hx]
  · intro x hx
    rw [Submodule.mem_bot] at hx
    simp [hx]
  · rintro c x y ⟨S₁, f₁, s₁, hx, b₁⟩ ⟨S₂, f₂, s₂, hy, b₂⟩
    refine ⟨S₁ ⊔ S₂, inferInstance, ?_, Submodule.add_mem_sup hx hy, ?_⟩
    · intro a b hab w hw
      obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hw
      rw [map_add]
      exact Submodule.add_mem_sup (s₁ a b hab u hu) (s₂ a b hab v hv)
    · exact quadForm_le_on_sup _ (GlobalTheory.T.casK_isSymmetric_and_inner_re_eq M n ε E hU).1 _ S₁ S₂
        (casK_mem_of_compact_stable ε E S₁ s₁) (casK_mem_of_compact_stable ε E S₂ s₂) b₁ b₂
  · rintro c a x ⟨S, f, s, hx, b⟩
    exact ⟨S, f, s, S.smul_mem a hx, b⟩
  · rintro c c' x hc hcc ⟨S, f, s, hx, b⟩
    refine ⟨S, f, s, hx, fun y hy => (b y hy).trans ?_⟩
    gcongr

end GlobalTheory
