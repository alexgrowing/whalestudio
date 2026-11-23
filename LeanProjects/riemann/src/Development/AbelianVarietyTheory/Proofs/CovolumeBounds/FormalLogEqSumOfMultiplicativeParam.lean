import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NatCastMulCoeffOfPderivEq
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FormalExpMulFormalExpNeg

namespace GlobalTheory.FormalCalc

open MvPowerSeries Sum

variable {σ τ ι κ μ A : Type*} [CommRing A]

section Tools

theorem subst_subst [Finite ι] {a : ι → MvPowerSeries κ A} {b : κ → MvPowerSeries μ A}
    (hb : HasSubst b) (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries ι A) :
    subst b (subst a f) = subst (fun i => subst b (a i)) f :=
  subst_comp_subst_apply (hasSubst_of_constantCoeff_zero ha) hb f

theorem subst_sumElim (b : κ → MvPowerSeries μ A) (u : σ → MvPowerSeries κ A)
    (t : τ → MvPowerSeries κ A) :
    (fun i => subst b (Sum.elim u t i)) =
      Sum.elim (fun i => subst b (u i)) fun j => subst b (t j) := by
  funext i; cases i <;> rfl

theorem subst_elim_X (f : MvPowerSeries (σ ⊕ τ) A) :
    subst (Sum.elim (fun i => X (inl i)) fun j => X (inr j) :
      σ ⊕ τ → MvPowerSeries (σ ⊕ τ) A) f = f := by
  have : (Sum.elim (fun i => X (inl i)) fun j => X (inr j) :
      σ ⊕ τ → MvPowerSeries (σ ⊕ τ) A) = X := by funext i; cases i <;> rfl
  rw [this, subst_self, id]

theorem subst_elim_elim_X (f : MvPowerSeries (σ ⊕ τ ⊕ ι) A) :
    subst (Sum.elim (fun i => X (inl i)) (Sum.elim (fun j => X (inr (inl j)))
      fun j => X (inr (inr j))) : σ ⊕ τ ⊕ ι → MvPowerSeries (σ ⊕ τ ⊕ ι) A) f = f := by
  have : (Sum.elim (fun i => X (inl i)) (Sum.elim (fun j => X (inr (inl j)))
      fun j => X (inr (inr j))) : σ ⊕ τ ⊕ ι → MvPowerSeries (σ ⊕ τ ⊕ ι) A) = X := by
    funext i; rcases i with i | i | i <;> rfl
  rw [this, subst_self, id]

theorem pderiv_subst' [Fintype ι] {a : ι → MvPowerSeries κ A}
    (ha : ∀ i, constantCoeff (a i) = 0) (f : MvPowerSeries ι A) (j : κ) :
    pderiv A j (subst a f) = ∑ i, subst a (pderiv A i f) * pderiv A j (a i) :=
  pderiv_subst (hasSubst_of_constantCoeff_zero ha) f j

theorem pderiv_X_ite [DecidableEq κ] (i j : κ) :
    pderiv A i (X j : MvPowerSeries κ A) = if j = i then 1 else 0 := by
  split_ifs with h
  · rw [h, pderiv_X_self]
  · exact pderiv_X_of_ne h

open Classical in

theorem coeff_subst_kill (e : ι → κ) {b : κ → MvPowerSeries κ A} (hb0 : ∀ i, b (e i) = 0)
    (hb1 : ∀ k, k ∉ Set.range e → b k = X k) (f : MvPowerSeries κ A) (α : κ →₀ ℕ) :
    coeff α (subst b f) = if ∀ i, α (e i) = 0 then coeff α f else 0 := by
  have hb : b = (fun k => if k ∈ Set.range e then (0 : A) else 1) • X := by
    funext k
    by_cases hk : k ∈ Set.range e
    · obtain ⟨i, rfl⟩ := hk
      simp [hb0]
    · simp only [Pi.smul_apply', hb1 k hk, if_neg hk, one_smul]
  rw [hb, ← rescale_eq_subst, coeff_rescale]
  split_ifs with h
  · rw [Finsupp.prod, Finset.prod_eq_one, one_mul]
    intro k hk
    rw [if_neg, one_pow]
    rintro ⟨i, rfl⟩
    exact Finsupp.mem_support_iff.mp hk (h i)
  · push Not at h
    obtain ⟨i, hi⟩ := h
    rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hi), zero_mul]
    rw [if_pos ⟨i, rfl⟩, zero_pow hi]

theorem ext_of_pderiv_of_subst [IsAddTorsionFree A] (e : ι → κ) {b : κ → MvPowerSeries κ A}
    (hb0 : ∀ i, b (e i) = 0) (hb1 : ∀ k, k ∉ Set.range e → b k = X k)
    {f g : MvPowerSeries κ A} (hD : ∀ i, pderiv A (e i) f = pderiv A (e i) g)
    (h0 : subst b f = subst b g) : f = g := by
  refine ext_of_pderiv_of_coeff e hD fun α hα => ?_
  have := congrArg (coeff α) h0
  rwa [coeff_subst_kill e hb0 hb1, coeff_subst_kill e hb0 hb1, if_pos hα, if_pos hα] at this

theorem subst_elim_zero_eq_zero_iff [Finite σ] [Finite τ] (f : MvPowerSeries (σ ⊕ τ) A) :
    subst (Sum.elim (fun _ => 0) X : σ ⊕ τ → MvPowerSeries τ A) f = 0 ↔
      ∀ α : σ ⊕ τ →₀ ℕ, (∀ i, α (inl i) = 0) → coeff α f = 0 := by
  have hk := coeff_subst_kill (A := A) (inl : σ → σ ⊕ τ)
    (b := Sum.elim (fun _ => 0) fun j => X (inr j)) (by simp) (by simp) f
  constructor
  · intro h α hα
    have hb : HasSubst (fun j => X (inr j) : τ → MvPowerSeries (σ ⊕ τ) A) :=
      hasSubst_of_constantCoeff_zero (by simp)
    have h2 := congrArg (subst (fun j => X (inr j) : τ → MvPowerSeries (σ ⊕ τ) A)) h
    simp [subst_subst hb, subst_sumElim, subst_X hb, subst_zero' hb] at h2
    rw [← if_pos hα (t := coeff α f) (e := 0), ← hk, h2, map_zero]
  · intro h
    have h1 : subst (Sum.elim (fun _ => 0) fun j => X (inr j) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ τ) A) f = 0 := by
      ext α
      rw [hk]
      split_ifs with hα
      · simp [h α hα]
      · simp
    have hb : HasSubst (Sum.elim (fun _ => 0) X : σ ⊕ τ → MvPowerSeries τ A) :=
      hasSubst_of_constantCoeff_zero (by simp)
    have h2 := congrArg (subst (Sum.elim (fun _ => 0) X : σ ⊕ τ → MvPowerSeries τ A)) h1
    simpa [subst_subst hb, subst_sumElim, subst_X hb, subst_zero' hb] using h2

theorem existsUnique_primitive_sum [Finite σ] [Finite τ] [Algebra ℚ A]
    (a : σ → MvPowerSeries (σ ⊕ τ) A)
    (ha : ∀ i j, pderiv A (inl i) (a j) = pderiv A (inl j) (a i)) :
    ∃! f : MvPowerSeries (σ ⊕ τ) A,
      subst (Sum.elim (fun _ => 0) X : σ ⊕ τ → MvPowerSeries τ A) f = 0 ∧
        ∀ i, pderiv A (inl i) f = a i := by
  simp only [subst_elim_zero_eq_zero_iff]
  exact existsUnique_primitive_param inl_injective a ha

end Tools

section Additive

variable [IsAddTorsionFree A]

theorem eq_sum_of_additive_param [Fintype σ] [Finite τ] {f : MvPowerSeries (σ ⊕ τ) A}
    (h : subst (Sum.elim (fun i => X (inl i) + X (inr (inl i))) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) f =
      subst (Sum.elim (fun i => X (inl i)) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) f +
      subst (Sum.elim (fun i => X (inr (inl i))) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) f) :
    f = ∑ i, X (inl i) * subst (fun j => X (inr j) : τ → MvPowerSeries (σ ⊕ τ) A)
      (subst (Sum.elim (fun _ => 0) X : σ ⊕ τ → MvPowerSeries τ A) (pderiv A (inl i) f)) := by
  classical
  have := Fintype.ofFinite τ
  have hb : HasSubst (Sum.elim (fun i => X (inl i)) (Sum.elim (fun _ => 0) fun j => X (inr j)) :
      σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ τ) A) := hasSubst_of_constantCoeff_zero (by simp)
  have hc : HasSubst (fun j => X (inr j) : τ → MvPowerSeries (σ ⊕ τ) A) :=
    hasSubst_of_constantCoeff_zero (by simp)
  have hd : HasSubst (Sum.elim (fun _ => 0) fun j => X (inr j) :
      σ ⊕ τ → MvPowerSeries (σ ⊕ τ) A) := hasSubst_of_constantCoeff_zero (by simp)
  refine ext_of_pderiv_of_subst inl (b := Sum.elim (fun _ => 0) fun j => X (inr j))
    (by simp) (by simp) (fun i => ?_) ?_
  · have h1 := congrArg (pderiv A (inr (inl i))) h
    simp [pderiv_subst', pderiv_X_ite] at h1
    have h2 := congrArg (subst (Sum.elim (fun i => X (inl i))
      (Sum.elim (fun _ => 0) fun j => X (inr j)) : σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ τ) A)) h1
    simp [subst_subst hb, subst_sumElim, subst_X hb, subst_add hb, subst_elim_X] at h2
    conv_lhs => rw [h2]
    simp [pderiv_subst', pderiv_X_ite, subst_subst hc, subst_sumElim, subst_X hc, subst_zero' hc]
  · have h2 := congrArg (subst (Sum.elim (fun i => X (inl i))
      (Sum.elim (fun _ => 0) fun j => X (inr j)) : σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ τ) A)) h
    simp [subst_subst hb, subst_sumElim, subst_X hb, subst_add hb, subst_elim_X] at h2
    simp [h2, subst_sum' hd, subst_mul hd, subst_X hd]

end Additive

section Cocycle

variable [Algebra ℚ A]

theorem existsUnique_coboundary_param [Finite σ] [Finite τ] {B : MvPowerSeries (σ ⊕ σ ⊕ τ) A}
    (h0 : subst (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) X) :
        σ ⊕ σ ⊕ τ → MvPowerSeries τ A) B = 0)
    (hsymm : subst (Sum.elim (fun i => X (inr (inl i))) (Sum.elim (fun i => X (inl i)) fun j => X (inr (inr j))) :
        σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) B = B)
    (hcoc : subst (Sum.elim (fun i => X (inl i))
        (Sum.elim (fun i => X (inr (inl i))) fun j => X (inr (inr (inr j)))) :
        σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ σ ⊕ τ) A) B +
      subst (Sum.elim (fun i => X (inl i) + X (inr (inl i)))
        (Sum.elim (fun i => X (inr (inr (inl i)))) fun j => X (inr (inr (inr j)))) :
        σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ σ ⊕ τ) A) B =
      subst (Sum.elim (fun i => X (inr (inl i)))
        (Sum.elim (fun i => X (inr (inr (inl i)))) fun j => X (inr (inr (inr j)))) :
        σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ σ ⊕ τ) A) B +
      subst (Sum.elim (fun i => X (inl i))
        (Sum.elim (fun i => X (inr (inl i)) + X (inr (inr (inl i)))) fun j => X (inr (inr (inr j)))) :
        σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ σ ⊕ τ) A) B) :
    ∃! k : MvPowerSeries (σ ⊕ τ) A, subst (Sum.elim (fun _ => 0) X : σ ⊕ τ → MvPowerSeries τ A) k = 0 ∧
      (∀ i, subst (Sum.elim (fun _ => 0) X : σ ⊕ τ → MvPowerSeries τ A) (pderiv A (inl i) k) = 0) ∧
      B = subst (Sum.elim (fun i => X (inl i) + X (inr (inl i))) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) k -
      subst (Sum.elim (fun i => X (inl i)) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) k -
      subst (Sum.elim (fun i => X (inr (inl i))) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) k := by
  classical
  have := Fintype.ofFinite σ
  have := Fintype.ofFinite τ
  have : IsAddTorsionFree A := .of_module_rat A

  have hz : HasSubst (Sum.elim (fun i => X (inl i)) (Sum.elim (fun i => X (inr (inl i))) (Sum.elim (fun _ => 0) fun j => X (inr (inr j)))) :
        σ ⊕ σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) := hasSubst_of_constantCoeff_zero (by simp)
  have hyz : HasSubst (Sum.elim (fun i => X (inl i)) (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) fun j => X (inr (inr j)))) :
        σ ⊕ σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) := hasSubst_of_constantCoeff_zero (by simp)
  have hxy : HasSubst (Sum.elim (fun i => X (inl i) + X (inr (inl i))) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) := hasSubst_of_constantCoeff_zero (by simp)
  have hx : HasSubst (Sum.elim (fun i => X (inl i)) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) := hasSubst_of_constantCoeff_zero (by simp)
  have hy : HasSubst (Sum.elim (fun i => X (inr (inl i))) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) := hasSubst_of_constantCoeff_zero (by simp)
  have hsw : HasSubst (Sum.elim (fun i => X (inr (inl i))) (Sum.elim (fun i => X (inl i)) fun j => X (inr (inr j))) :
        σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) := hasSubst_of_constantCoeff_zero (by simp)
  have hy0 : HasSubst (Sum.elim (fun i => X (inl i)) (Sum.elim (fun _ => 0) fun j => X (inr j)) :
        σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ τ) A) := hasSubst_of_constantCoeff_zero (by simp)
  have hy3 : HasSubst (Sum.elim (fun i => X (inl i)) (Sum.elim (fun _ => 0) fun j => X (inr (inr j))) :
        σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) := hasSubst_of_constantCoeff_zero (by simp)
  have h00 : HasSubst (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) X) :
        σ ⊕ σ ⊕ τ → MvPowerSeries τ A) := hasSubst_of_constantCoeff_zero (by simp)
  have ht : HasSubst (fun j => X (inr (inr j)) : τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) := hasSubst_of_constantCoeff_zero (by simp)
  have hz2 : HasSubst (Sum.elim (fun _ => 0) X : σ ⊕ τ → MvPowerSeries τ A) := hasSubst_of_constantCoeff_zero (by simp)
  obtain ⟨a, ha⟩ : ∃ a : σ → MvPowerSeries (σ ⊕ τ) A, ∀ i, a i =
      subst (Sum.elim (fun i => X (inl i)) (Sum.elim (fun _ => 0) fun j => X (inr j)) :
        σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ τ) A) (pderiv A (inr (inl i)) B) :=
    ⟨_, fun _ => rfl⟩
  have hP (i : σ) : pderiv A (inr (inl i)) B =
      subst (Sum.elim (fun i => X (inl i) + X (inr (inl i))) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) (a i) - subst (Sum.elim (fun i => X (inr (inl i))) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) (a i) := by
    have h1 := congrArg (pderiv A (inr (inr (inl i)))) hcoc
    simp [pderiv_subst', pderiv_X_ite] at h1
    have h2 := congrArg (subst (Sum.elim (fun i => X (inl i)) (Sum.elim (fun i => X (inr (inl i))) (Sum.elim (fun _ => 0) fun j => X (inr (inr j)))) :
        σ ⊕ σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A)) h1
    simp [subst_subst hz, subst_X hz, subst_add hz, subst_sub hz, subst_zero' hz, subst_sumElim, subst_elim_elim_X] at h2
    simp [ha, subst_subst hxy, subst_X hxy, subst_add hxy, subst_sub hxy, subst_zero' hxy, subst_subst hy, subst_X hy, subst_add hy, subst_sub hy, subst_zero' hy, subst_sumElim, h2]
  have hQ (i : σ) : pderiv A (inl i) B =
      subst (Sum.elim (fun i => X (inl i) + X (inr (inl i))) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) (a i) - subst (Sum.elim (fun i => X (inl i)) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) (a i) := by
    have h1 := congrArg (pderiv A (inl i)) hsymm
    simp [pderiv_subst', pderiv_X_ite] at h1
    rw [← h1, hP]
    simp [subst_subst hsw, subst_X hsw, subst_add hsw, subst_sub hsw, subst_zero' hsw, subst_sumElim, add_comm]
  have hclosed (i j : σ) : pderiv A (inl i) (a j) = pderiv A (inl j) (a i) := by
    have h1 := pderiv_comm (inl i) (inr (inl j)) B
    rw [hP, hQ] at h1
    simp [pderiv_subst', pderiv_X_ite] at h1
    have h2 := congrArg (subst (Sum.elim (fun i => X (inl i)) (Sum.elim (fun _ => 0) fun j => X (inr j)) :
        σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ τ) A)) h1
    simpa [subst_subst hy0, subst_X hy0, subst_add hy0, subst_sub hy0, subst_zero' hy0, subst_sumElim, subst_elim_X] using h2
  have ha0 (i : σ) : subst (Sum.elim (fun _ => 0) X : σ ⊕ τ → MvPowerSeries τ A) (a i) = 0 := by
    have h1 := congrArg (subst (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) X) :
        σ ⊕ σ ⊕ τ → MvPowerSeries τ A)) (hP i)
    simp [subst_subst h00, subst_X h00, subst_add h00, subst_sub h00, subst_zero' h00, subst_sumElim] at h1
    simpa [ha, subst_subst hz2, subst_X hz2, subst_add hz2, subst_sub hz2, subst_zero' hz2, subst_sumElim] using h1
  obtain ⟨k, ⟨hk0, hk⟩, -⟩ := existsUnique_primitive_sum a hclosed
  have hB : B = subst (Sum.elim (fun i => X (inl i) + X (inr (inl i))) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) k -
      subst (Sum.elim (fun i => X (inl i)) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) k -
      subst (Sum.elim (fun i => X (inr (inl i))) fun j => X (inr (inr j)) :
        σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A) k := by
    refine ext_of_pderiv_of_subst (fun i : σ => (inr (inl i) : σ ⊕ σ ⊕ τ))
      (b := Sum.elim (fun i => X (inl i)) (Sum.elim (fun _ => 0) fun j => X (inr (inr j)))) (by simp) (by simp) (fun i => ?_) ?_
    · simp [pderiv_subst', pderiv_X_ite, hk, hP]
    · have h1 := congrArg (subst (Sum.elim (fun i => X (inl i)) (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) fun j => X (inr (inr j)))) :
        σ ⊕ σ ⊕ σ ⊕ τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A)) hcoc
      have h2 := congrArg (subst (fun j => X (inr (inr j)) : τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A)) h0
      have h3 := congrArg (subst (fun j => X (inr (inr j)) : τ → MvPowerSeries (σ ⊕ σ ⊕ τ) A)) hk0
      simp [subst_subst ht, subst_X ht, subst_add ht, subst_sub ht, subst_zero' ht, subst_sumElim] at h2 h3
      simp [subst_subst hyz, subst_X hyz, subst_add hyz, subst_sub hyz, subst_zero' hyz, subst_sumElim, h2] at h1
      simp [subst_subst hy3, subst_X hy3, subst_add hy3, subst_sub hy3, subst_zero' hy3, subst_sumElim, h1, h3]
  refine ⟨k, ⟨hk0, fun i => by rw [hk, ha0], hB⟩, ?_⟩
  rintro k' ⟨-, hk1, hk2⟩
  have hd := eq_sum_of_additive_param (f := k' - k) (by
    rw [subst_sub hxy, subst_sub hx, subst_sub hy]
    linear_combination hB - hk2)
  rw [← sub_eq_zero, hd]
  simp [subst_sub hz2, hk1, hk, ha0, subst_zero' (hasSubst_of_constantCoeff_zero (by simp) :
    HasSubst (fun j => X (inr j) : τ → MvPowerSeries (σ ⊕ τ) A))]

end Cocycle

end GlobalTheory.FormalCalc
