import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.LiftCommEAt

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz.CtrX

open PositivityTheory.Rg.Cz

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

def reIx {P Q : Type} (e : P ≃ Q) (ξ : TV n M P) : TV n M Q := fun I => ξ (I ∘ e)

def unc {A B : Type} (f : TV n (TV n M A) B) : TV n M (A ⊕ B) := fun I => f (I ∘ Sum.inr) (I ∘ Sum.inl)

def cur {A B : Type} (g : TV n M (A ⊕ B)) : TV n (TV n M A) B := fun J K => g (Sum.elim K J)

theorem unc_cur {A B : Type} (g : TV n M (A ⊕ B)) : unc (cur g) = g := by
  funext I
  simp only [unc, cur, Sum.elim_comp_inl_inr]

theorem unc_inj {A B : Type} {f g : TV n (TV n M A) B} (h : unc f = unc g) : f = g := by
  funext J K
  have := congrFun h (Sum.elim K J)
  simpa [unc] using this

theorem unc_smul {A B : Type} (c : ℂ) (f : TV n (TV n M A) B) : unc (c • f) = c • unc f := rfl

theorem reIx_smul {P Q : Type} (e : P ≃ Q) (c : ℂ) (ξ : TV n M P) : reIx e (c • ξ) = c • reIx e ξ := rfl

theorem actT_reIx {ι Γ P Q : Type} [Fintype P] [DecidableEq P] [Fintype Q] [DecidableEq Q] (e : P ≃ Q)
    (lab : P → ι) (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M) (γ : Γ) (ξ : TV n M P) :
    actT (lab ∘ e.symm) κ ρ γ (reIx e ξ) = reIx e (actT lab κ ρ γ ξ) := by
  funext I
  simp only [actT, reIx, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, Function.comp_apply]
  symm
  refine Fintype.sum_equiv (e.arrowCongr (Equiv.refl (Fin n))) _ _ (fun J => ?_)
  have hJ : (e.arrowCongr (Equiv.refl (Fin n)) J) ∘ e = J := by
    funext p
    simp [Equiv.arrowCongr_apply]
  rw [hJ]
  congr 1
  refine Fintype.prod_equiv e _ _ (fun p => ?_)
  simp [Equiv.arrowCongr_apply]

theorem actT_unc {ι Γ A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] (la : A → ι) (lb : B → ι)
    (κ : ι → Γ → Matrix (Fin n) (Fin n) ℂ) (ρ : Γ → Module.End ℂ M) (γ : Γ) (f : TV n (TV n M A) B) :
    actT (Sum.elim la lb) κ ρ γ (unc f) = unc (actT lb κ (actT la κ ρ) γ f) := by
  funext I
  simp only [actT, unc, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply, Function.comp_apply, Finset.sum_apply, Pi.smul_apply]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv ((Equiv.sumArrowEquivProdArrow A B (Fin n)).trans (Equiv.prodComm _ _)) _ _ (fun d => ?_)
  simp only [Equiv.trans_apply, Equiv.prodComm_apply, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
  rw [mul_comm]
  rfl

def splitE (m n : ℕ) (h : n ≤ m) : Fin m ≃ Fin (m - n) ⊕ Fin n where
  toFun i := if hi : (i : ℕ) < n then Sum.inr ⟨i, hi⟩ else Sum.inl ⟨i - n, by omega⟩
  invFun := Sum.elim (fun j => ⟨j + n, by omega⟩) (fun j => ⟨j, by omega⟩)
  left_inv i := by
    by_cases hi : (i : ℕ) < n
    · simp [hi]
    · simp only [hi, dite_false, Sum.elim_inl]
      ext; simp; omega
  right_inv x := by
    rcases x with j | j
    · simp
    · simp [j.2]

theorem pm_alt_firstG {m k : ℕ} (τ : Equiv.Perm (Fin m)) (hτ : τ ∈ firstG m k) (x : TV n M (Fin m)) :
    pm τ (alt (firstG m k) x) = ((Equiv.Perm.sign τ : ℤ) : ℂ) • alt (firstG m k) x := by
  have hmem : ∀ σ : Equiv.Perm (Fin m), σ ∈ firstG m k ↔ ∀ j : Fin m, k ≤ (j : ℕ) → σ j = j := by
    intro σ
    simp [firstG]
  have hτ' := (hmem τ).1 hτ
  have hmul : ∀ σ : Equiv.Perm (Fin m), pm τ (pm σ x) = pm (τ * σ) x := by
    intro σ
    funext I
    rfl
  simp only [alt, LinearMap.sum_apply, map_sum, Finset.smul_sum, LinearMap.smul_apply, map_smul, hmul, smul_smul]
  refine Finset.sum_nbij' (fun σ => τ * σ) (fun σ => τ⁻¹ * σ) ?_ ?_ ?_ ?_ ?_
  · intro σ hσ
    rw [hmem] at hσ ⊢
    intro j hj
    simp [Equiv.Perm.mul_apply, hσ j hj, hτ' j hj]
  · intro σ hσ
    rw [hmem] at hσ ⊢
    intro j hj
    have h1 : τ⁻¹ j = j := by
      rw [Equiv.Perm.inv_eq_iff_eq]
      exact (hτ' j hj).symm
    simp [Equiv.Perm.mul_apply, hσ j hj, h1]
  · intro σ _
    simp
  · intro σ _
    simp
  · intro σ _
    congr 1
    rw [Equiv.Perm.sign_mul]
    rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h]

theorem cur_anti {m : ℕ} (h : n ≤ m) (η : TV n M (Fin m))
    (hη : ∀ τ ∈ firstG m n, pm τ η = ((Equiv.Perm.sign τ : ℤ) : ℂ) • η) (σ : Equiv.Perm (Fin n)) :
    pm σ (cur (reIx (splitE m n h) η)) = ((Equiv.Perm.sign σ : ℤ) : ℂ) • cur (reIx (splitE m n h) η) := by
  funext J K
  set e := splitE m n h with he
  let S : Equiv.Perm (Fin (m - n) ⊕ Fin n) := Equiv.sumCongr (Equiv.refl _) σ
  let τ : Equiv.Perm (Fin m) := (e.trans S).trans e.symm
  have hτ : τ ∈ firstG m n := by
    simp only [firstG, Finset.mem_filter, Finset.mem_univ, true_and]
    intro j hj
    have hj' : ¬ (j : ℕ) < n := by omega
    have ha : e j = Sum.inl ⟨(j : ℕ) - n, by omega⟩ := by
      simp [he, splitE, hj']
    show e.symm (S (e j)) = j
    rw [ha]
    exact e.symm_apply_eq.2 ha.symm
  have hs : Equiv.Perm.sign τ = Equiv.Perm.sign σ := by
    show Equiv.Perm.sign ((e.symm.symm.trans S).trans e.symm) = _
    rw [Equiv.Perm.sign_symm_trans_trans]
    simp [S, Equiv.Perm.sign_sumCongr]
  have key := congrFun (hη τ hτ) (Sum.elim K J ∘ e)
  simp only [pm, LinearMap.pi_apply, LinearMap.proj_apply, Pi.smul_apply] at key
  simp only [pm, cur, reIx, LinearMap.pi_apply, LinearMap.proj_apply, Pi.smul_apply]
  rw [← hs, ← key]
  congr 1
  funext x
  simp only [Function.comp_apply, τ, Equiv.trans_apply, Equiv.apply_symm_apply]
  generalize e x = y
  cases y <;> rfl

end PositivityTheory.Rg.Cz.CtrX

end
