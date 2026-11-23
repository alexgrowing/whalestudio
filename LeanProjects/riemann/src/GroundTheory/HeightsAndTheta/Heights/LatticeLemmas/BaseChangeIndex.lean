import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField TensorProduct

noncomputable section

variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]

theorem finrank_integers : Module.finrank (𝓞 K) (𝓞 L) = Module.finrank K L :=
  (IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L).symm

theorem card_tensor_quotient (I : Ideal (𝓞 K)) :
    Nat.card (𝓞 L ⊗[𝓞 K] (𝓞 K ⧸ I)) = Nat.card (𝓞 K ⧸ I) ^ Module.finrank K L := by
  rw [← Nat.card_congr (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (𝓞 L) I).toEquiv,
    ← Submodule.cardQuot_apply, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
    ← Ideal.absNorm_apply, Ideal.absNorm_algebraMap, finrank_integers]

theorem card_tensor_integers (Q : Type*) [AddCommGroup Q] [Module (𝓞 K) Q] [Finite Q] :
    Nat.card (𝓞 L ⊗[𝓞 K] Q) = Nat.card Q ^ Module.finrank K L := by
  induction hn : Nat.card Q using Nat.strong_induction_on generalizing Q with
  | _ n ih =>
  subst hn
  rcases subsingleton_or_nontrivial Q with hQ | hQ
  · have h0 : ∀ z : 𝓞 L ⊗[𝓞 K] Q, z = 0 := fun z ↦ by
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul b q => rw [Subsingleton.elim q 0, tmul_zero]
      | add a b ha hb => rw [ha, hb, add_zero]
    have : Subsingleton (𝓞 L ⊗[𝓞 K] Q) := ⟨fun x y ↦ by rw [h0 x, h0 y]⟩
    rw [Nat.card_of_subsingleton (0 : 𝓞 L ⊗[𝓞 K] Q), Nat.card_of_subsingleton (0 : Q), one_pow]
  obtain ⟨x, hx⟩ := exists_ne (0 : Q)
  set C : Submodule (𝓞 K) Q := Submodule.span (𝓞 K) {x}
  have : Finite (Q ⧸ C) := Finite.of_surjective _ (Submodule.mkQ_surjective C)
  have hCQ : Nat.card Q = Nat.card (Q ⧸ C) * Nat.card C :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup C.toAddSubgroup
  have hC1 : 1 < Nat.card C := by
    have : Nontrivial C := ⟨⟨⟨x, Submodule.mem_span_singleton_self x⟩, 0, fun h ↦ hx (congrArg Subtype.val h)⟩⟩
    exact Finite.one_lt_card
  have hlt : Nat.card (Q ⧸ C) < Nat.card Q := by
    have : 0 < Nat.card (Q ⧸ C) := Nat.card_pos
    rw [hCQ]
    exact lt_mul_of_one_lt_right this hC1
  have hquot := ih _ hlt (Q ⧸ C) rfl
  have hcyc : Nat.card (𝓞 L ⊗[𝓞 K] C) = Nat.card C ^ Module.finrank K L := by
    have e := Ideal.quotTorsionOfEquivSpanSingleton (𝓞 K) Q x
    rw [← Nat.card_congr e.toEquiv, ← card_tensor_quotient L,
      Nat.card_congr (LinearEquiv.lTensor (𝓞 L) e).toEquiv]
  set f : 𝓞 L ⊗[𝓞 K] C →ₗ[𝓞 K] 𝓞 L ⊗[𝓞 K] Q := LinearMap.lTensor (𝓞 L) C.subtype
  have hf : Function.Injective f :=
    Module.Flat.lTensor_preserves_injective_linearMap C.subtype C.injective_subtype
  have h1 : Nat.card (𝓞 L ⊗[𝓞 K] Q) =
      Nat.card ((𝓞 L ⊗[𝓞 K] Q) ⧸ LinearMap.range f) * Nat.card (LinearMap.range f) :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (LinearMap.range f).toAddSubgroup
  have h2 : Nat.card (LinearMap.range f) = Nat.card (𝓞 L ⊗[𝓞 K] C) :=
    Nat.card_congr (LinearEquiv.ofInjective f hf).toEquiv.symm
  have h3 : Nat.card ((𝓞 L ⊗[𝓞 K] Q) ⧸ LinearMap.range f) = Nat.card (𝓞 L ⊗[𝓞 K] (Q ⧸ C)) :=
    Nat.card_congr (TensorProduct.tensorQuotientEquiv (𝓞 L) C).toEquiv.symm
  rw [h1, h2, h3, hquot, hcyc, hCQ, mul_pow]

theorem card_extensions (σ : K →+* ℂ) :
    Nat.card {τ : L →+* ℂ // τ.comp (algebraMap K L) = σ} = Module.finrank K L := by
  let _ : Algebra K ℂ := σ.toAlgebra
  rw [← AlgHom.natCard_of_splits K L ℂ (fun _ ↦ IsAlgClosed.splits _)]
  exact Nat.card_congr
    { toFun := fun τ ↦ (⟨τ.1, fun a ↦ RingHom.congr_fun τ.2 a⟩ : L →ₐ[K] ℂ)
      invFun := fun g ↦ ⟨g.toRingHom, by
        ext a
        exact g.commutes a⟩
      left_inv := fun τ ↦ rfl
      right_inv := fun g ↦ rfl }

theorem sum_comp_algebraMap (f : (K →+* ℂ) → ℝ) :
    ∑ τ : L →+* ℂ, f (τ.comp (algebraMap K L)) = Module.finrank K L * ∑ σ : K →+* ℂ, f σ := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ (fun τ : L →+* ℂ ↦ τ.comp (algebraMap K L)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  rw [Finset.sum_congr rfl (fun τ hτ ↦ by rw [(Finset.mem_filter.mp hτ).2]), Finset.sum_const,
    nsmul_eq_mul, ← card_extensions L σ, Nat.card_eq_fintype_card, Fintype.card_subtype]

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
