import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasValK

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Intertwine

variable {M M' : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M'] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {E' : Fin n → Fin n → Module.End ℂ M'}

theorem layer_map_le (f : M →ₗ[ℂ] M') (hf : ∀ a b x, f (E a b x) = E' a b (f x)) {V : Submodule ℂ M}
    {V' : Submodule ℂ M'} (hV : ∀ x ∈ V, f x ∈ V') :
    ∀ k, ∀ x ∈ layer ε E V k, f x ∈ layer ε E' V' k
  | 0 => hV
  | k + 1 => by
    have ih := layer_map_le f hf hV k
    have hle : layer ε E V (k + 1) ≤ (layer ε E' V' (k + 1)).comap f := by
      show layer ε E V k ⊔ _ ≤ _
      refine sup_le (fun x hx => ?_) (iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_)
      · exact (le_sup_left : layer ε E' V' k ≤ layer ε E' V' k ⊔ _) (ih x hx)
      · rintro _ ⟨x, hx, rfl⟩
        show f (E a b x) ∈ layer ε E' V' k ⊔ _
        rw [hf]
        refine (le_sup_right : _ ≤ layer ε E' V' k ⊔ _) ?_
        exact Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem b
          (Submodule.mem_iSup_of_mem hab ⟨f x, ih x hx, rfl⟩))
    exact fun x hx => hle hx

theorem khw_map (f : M →ₗ[ℂ] M') (hf : ∀ a b x, f (E a b x) = E' a b (f x)) {μ : Fin n → ℝ} {w : M}
    (hw : IsKHWVec ε E μ w) : IsKHWVec ε E' μ (f w) :=
  ⟨fun a => by rw [← hf, hw.1 a, map_smul], fun a b hab hε => by rw [← hf, hw.2 a b hab hε, map_zero]⟩

theorem casimir_map (f : M →ₗ[ℂ] M') (hf : ∀ a b x, f (E a b x) = E' a b (f x)) (x : M) :
    f (casimir E x) = casimir E' (f x) := by
  simp [casimir, LinearMap.sum_apply, Module.End.mul_apply, map_sum, hf]

end Intertwine

section Prod

variable {M₁ M₂ : Type*} [AddCommGroup M₁] [Module ℂ M₁] [AddCommGroup M₂] [Module ℂ M₂]

def prodE (E₁ : Fin n → Fin n → Module.End ℂ M₁) (E₂ : Fin n → Fin n → Module.End ℂ M₂) :
    Fin n → Fin n → Module.End ℂ (WithLp 2 (M₁ × M₂)) := fun a b =>
  (WithLp.linearEquiv 2 ℂ (M₁ × M₂)).symm.toLinearMap ∘ₗ (LinearMap.prodMap (E₁ a b) (E₂ a b)) ∘ₗ
    (WithLp.linearEquiv 2 ℂ (M₁ × M₂)).toLinearMap

def prFst : WithLp 2 (M₁ × M₂) →ₗ[ℂ] M₁ := LinearMap.fst ℂ M₁ M₂ ∘ₗ (WithLp.linearEquiv 2 ℂ (M₁ × M₂)).toLinearMap

def prSnd : WithLp 2 (M₁ × M₂) →ₗ[ℂ] M₂ := LinearMap.snd ℂ M₁ M₂ ∘ₗ (WithLp.linearEquiv 2 ℂ (M₁ × M₂)).toLinearMap

@[simp] theorem prFst_apply (x : WithLp 2 (M₁ × M₂)) : prFst x = (WithLp.ofLp x).1 := rfl
@[simp] theorem prSnd_apply (x : WithLp 2 (M₁ × M₂)) : prSnd x = (WithLp.ofLp x).2 := rfl

theorem prod_ext {x y : WithLp 2 (M₁ × M₂)} (h₁ : prFst x = prFst y) (h₂ : prSnd x = prSnd y) : x = y :=
  WithLp.ofLp_injective 2 (Prod.ext h₁ h₂)

variable {E₁ : Fin n → Fin n → Module.End ℂ M₁} {E₂ : Fin n → Fin n → Module.End ℂ M₂}

theorem prFst_prodE (a b : Fin n) (x : WithLp 2 (M₁ × M₂)) : prFst (prodE E₁ E₂ a b x) = E₁ a b (prFst x) := rfl
theorem prSnd_prodE (a b : Fin n) (x : WithLp 2 (M₁ × M₂)) : prSnd (prodE E₁ E₂ a b x) = E₂ a b (prSnd x) := rfl

theorem isGlRep_prod (hE₁ : IsGlRep E₁) (hE₂ : IsGlRep E₂) : IsGlRep (prodE E₁ E₂) := by
  intro a b c d
  refine LinearMap.ext fun x => prod_ext ?_ ?_
  · have h := congrArg (fun X : Module.End ℂ M₁ => X (prFst x)) (hE₁ a b c d)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    change prFst _ = prFst _
    simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, prFst_prodE]
    rw [h]
    split_ifs <;> simp <;> rfl
  · have h := congrArg (fun X : Module.End ℂ M₂ => X (prSnd x)) (hE₂ a b c d)
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    change prSnd _ = prSnd _
    simp only [LinearMap.sub_apply, Module.End.mul_apply, map_sub, prSnd_prodE]
    rw [h]
    split_ifs <;> simp <;> rfl

end Prod

section ProdUnitary

variable {M₁ M₂ : Type*} [NormedAddCommGroup M₁] [InnerProductSpace ℂ M₁] [NormedAddCommGroup M₂]
  [InnerProductSpace ℂ M₂] {ε : Fin n → Bool}
  {E₁ : Fin n → Fin n → Module.End ℂ M₁} {E₂ : Fin n → Fin n → Module.End ℂ M₂}

theorem isInfUnitary_prod (hU₁ : IsInfUnitary ε E₁) (hU₂ : IsInfUnitary ε E₂) :
    IsInfUnitary ε (prodE E₁ E₂) := by
  intro a b x y
  have h₁ := hU₁ a b (prFst x) (prFst y)
  have h₂ := hU₂ a b (prSnd x) (prSnd y)
  simp only [WithLp.prod_inner_apply]
  change inner ℂ (prFst (prodE E₁ E₂ a b x)) (prFst y) + inner ℂ (prSnd (prodE E₁ E₂ a b x)) (prSnd y) =
    adjSign ε a b * (inner ℂ (prFst x) (prFst (prodE E₁ E₂ b a y)) +
      inner ℂ (prSnd x) (prSnd (prodE E₁ E₂ b a y)))
  rw [prFst_prodE, prSnd_prodE, prFst_prodE, prSnd_prodE, h₁, h₂, mul_add]

end ProdUnitary

end ReciprocityTheory.ChartRestriction.DS
