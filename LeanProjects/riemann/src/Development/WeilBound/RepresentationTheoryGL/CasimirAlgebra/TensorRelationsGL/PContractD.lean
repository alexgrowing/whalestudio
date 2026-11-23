import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.LiftCommEAt

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz.CtrX

open PositivityTheory.Rg.Cz

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

theorem antisymmetric_eq_zero_of_not_injective (f : TV n M (Fin n))
    (hf : ∀ σ : Equiv.Perm (Fin n), pm σ f = ((Equiv.Perm.sign σ : ℤ) : ℂ) • f) (J : Fin n → Fin n)
    (hJ : ¬ Function.Injective J) : f J = 0 := by
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hJ
  have h2 : J ∘ ⇑(Equiv.swap i j) = J := by
    funext k
    simp only [Function.comp]
    rcases eq_or_ne k i with rfl | hki
    · simp [hij]
    rcases eq_or_ne k j with rfl | hkj
    · simp [hij]
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have h1 := congrFun (hf (Equiv.swap i j)) J
  have h3 : pm (Equiv.swap i j) f J = f J := by
    show f (J ∘ ⇑(Equiv.swap i j)) = f J
    rw [h2]
  rw [h3, Pi.smul_apply, Equiv.Perm.sign_swap hne] at h1
  have h4 : (2 : ℂ) • f J = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h1]
    simp
  rcases smul_eq_zero.mp h4 with h | h
  · norm_num at h
  · exact h

theorem anti_span (f : TV n M (Fin n))
    (hf : ∀ σ : Equiv.Perm (Fin n), pm σ f = ((Equiv.Perm.sign σ : ℤ) : ℂ) • f) (J : Fin n → Fin n) :
    ∃ c : ℂ, f J = c • f id := by
  by_cases hJ : Function.Injective J
  · have hb : Function.Bijective J := Finite.injective_iff_bijective.mp hJ
    refine ⟨((Equiv.Perm.sign (Equiv.ofBijective J hb) : ℤ) : ℂ), ?_⟩
    have h1 := congrFun (hf (Equiv.ofBijective J hb)) id
    have h3 : pm (Equiv.ofBijective J hb) f id = f J := rfl
    rw [h3, Pi.smul_apply] at h1
    exact h1
  · exact ⟨0, by rw [antisymmetric_eq_zero_of_not_injective f hf J hJ, zero_smul]⟩

theorem actT_anti_id {ι Γ : Type} (τ : ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M) (γ : Γ)
    (f : TV n M (Fin n)) (hf : ∀ σ : Equiv.Perm (Fin n), pm σ f = ((Equiv.Perm.sign σ : ℤ) : ℂ) • f) :
    actT (fun _ : Fin n => τ) κ ρ γ f id = (κ τ γ).det • ρ γ (f id) := by
  set A := κ τ γ with hA
  have hsum : actT (fun _ : Fin n => τ) κ ρ γ f id
      = ∑ J : Fin n → Fin n, (∏ p, A p (J p)) • ρ γ (f J) := by
    simp only [actT, LinearMap.pi_apply, LinearMap.sum_apply,
      LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, id, hA]
  have hperm : ∀ σ : Equiv.Perm (Fin n), f ⇑σ = ((Equiv.Perm.sign σ : ℤ) : ℂ) • f id := by
    intro σ
    have h1 := congrFun (hf σ) id
    rw [Pi.smul_apply] at h1
    exact h1
  have hsub : ∑ J ∈ Finset.univ.image (fun σ : Equiv.Perm (Fin n) => (⇑σ : Fin n → Fin n)),
        (∏ p, A p (J p)) • ρ γ (f J)
      = ∑ J : Fin n → Fin n, (∏ p, A p (J p)) • ρ γ (f J) := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro J _ hJ
    have hni : ¬ Function.Injective J := by
      intro hinj
      apply hJ
      rw [Finset.mem_image]
      exact ⟨Equiv.ofBijective J (Finite.injective_iff_bijective.mp hinj), Finset.mem_univ _, rfl⟩
    rw [antisymmetric_eq_zero_of_not_injective f hf J hni, map_zero, smul_zero]
  rw [hsum, ← hsub, Finset.sum_image (fun σ _ τ' _ h => Equiv.coe_fn_injective h)]
  simp_rw [hperm, map_smul, smul_smul]
  rw [← Finset.sum_smul, ← Matrix.det_transpose, Matrix.det_apply']
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  rw [mul_comm]
  rfl

end PositivityTheory.Rg.Cz.CtrX

end
