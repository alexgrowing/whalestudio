import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.EvalMC

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.Lap.EvalC

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

section Alg

variable {𝒰 : Type*} [Ring 𝒰] [Algebra ℂ 𝒰]

theorem cminor_reindex {n n' : ℕ} (F : Fin n → Fin n → 𝒰) (e : Fin n' → Fin n) (he : Function.Injective e)
    {p : ℕ} (R C : Fin p → Fin n') (x : ℂ) :
    cminor (fun a b => F (e a) (e b)) R C x = cminor F (e ∘ R) (e ∘ C) x := by
  unfold cminor capEntry
  simp only [Function.comp_apply, he.eq_iff]

theorem cminor_cast {n p p' : ℕ} (h : p = p') (F : Fin n → Fin n → 𝒰) (R C : Fin p' → Fin n) (x : ℂ) :
    cminor F (R ∘ Fin.cast h) (C ∘ Fin.cast h) x = cminor F R C x := by
  subst h; rfl

theorem sign_mul_self_C {p : ℕ} (σ : Equiv.Perm (Fin p)) :
    ((Equiv.Perm.sign σ : ℤˣ) : ℂ) * ((Equiv.Perm.sign σ : ℤˣ) : ℂ) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp

theorem cminor_frameAB_minor {m : ℕ} (E : Fin (m + 1) → Fin (m + 1) → 𝒰) (hE : GlRelR E)
    (A B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (hAB : A * B = 1) (a b : Fin (m + 1)) (x : ℂ) :
    cminor (frameAB A B E) a.succAbove b.succAbove x = ∑ c : Fin (m + 1), ∑ d : Fin (m + 1),
      ((A.submatrix a.succAbove c.succAbove).det * (B.submatrix d.succAbove b.succAbove).det) •
        cminor E c.succAbove d.succAbove x := by
  set f : ℂ := ((m.factorial : ℕ) : ℂ)
  have hf : f * f ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m))
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m))
  suffices key : (f * f) • cminor (frameAB A B E) a.succAbove b.succAbove x = (f * f) •
      ∑ c : Fin (m + 1), ∑ d : Fin (m + 1),
        ((A.submatrix a.succAbove c.succAbove).det * (B.submatrix d.succAbove b.succAbove).det) •
          cminor E c.succAbove d.succAbove x by
    have := congrArg (fun y => (f * f)⁻¹ • y) key
    simpa only [inv_smul_smul₀ hf] using this
  rw [cminor_frameAB_cb E hE A B hAB]
  rw [sum_symm_inj (fun ρ => ∑ τ : Fin m → Fin (m + 1),
      ((A.submatrix a.succAbove ρ).det * (B.submatrix τ b.succAbove).det) • cminor E ρ τ x)]
  · rw [mul_smul]
    congr 1
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [sum_symm_inj (fun τ => ((A.submatrix a.succAbove c.succAbove).det * (B.submatrix τ b.succAbove).det) •
      cminor E c.succAbove τ x)]
    · intro τ σ
      have h1 : B.submatrix (τ ∘ σ) b.succAbove = (B.submatrix τ b.succAbove).submatrix σ id := rfl
      simp only [h1, Matrix.det_permute]
      rw [cminor_perm_cols E hE, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
      congr 1
      linear_combination ((A.submatrix a.succAbove c.succAbove).det * (B.submatrix τ b.succAbove).det) *
        sign_mul_self_C σ
    · intro τ hτ
      have : (B.submatrix τ b.succAbove).det = 0 := by
        simp only [Function.Injective, not_forall] at hτ
        obtain ⟨i, j, hij, hne⟩ := hτ
        exact Matrix.det_zero_of_row_eq hne (by funext l; simp [hij])
      simp [this]
  · intro ρ σ
    have h1 : A.submatrix a.succAbove (ρ ∘ σ) = (A.submatrix a.succAbove ρ).submatrix id σ := rfl
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [h1, Matrix.det_permute']
    rw [cminor_perm_rows E, ← Int.cast_smul_eq_zsmul ℂ, smul_smul]
    congr 1
    linear_combination ((A.submatrix a.succAbove ρ).det * (B.submatrix τ b.succAbove).det) * sign_mul_self_C σ
  · intro ρ hρ
    have : (A.submatrix a.succAbove ρ).det = 0 := by
      simp only [Function.Injective, not_forall] at hρ
      obtain ⟨i, j, hij, hne⟩ := hρ
      exact Matrix.det_zero_of_column_eq hne (fun l => by simp [hij])
    simp [this]

end Alg

section Cov

theorem adjugate_eq_of_mul {n : ℕ} (g g' : Matrix (Fin n) (Fin n) ℂ) (h : g' * g = 1) :
    Matrix.adjugate g = g.det • g' := by
  calc Matrix.adjugate g = (g' * g) * Matrix.adjugate g := by rw [h, Matrix.one_mul]
    _ = g' * (g * Matrix.adjugate g) := by rw [Matrix.mul_assoc]
    _ = g' * (g.det • (1 : Matrix (Fin n) (Fin n) ℂ)) := by rw [Matrix.mul_adjugate]
    _ = g.det • g' := by rw [Matrix.mul_smul, Matrix.mul_one]

theorem neg_one_pow_mul_self (k : ℕ) : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
  rw [← mul_pow]; simp

theorem det_sub_succAbove {m : ℕ} (g g' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (h : g' * g = 1)
    (i j : Fin (m + 1)) :
    (g.submatrix i.succAbove j.succAbove).det = (-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * (g.det * g' j i) := by
  have h1 := Matrix.adjugate_fin_succ_eq_det_submatrix g j i
  rw [adjugate_eq_of_mul g g' h, Matrix.smul_apply, smul_eq_mul] at h1
  rw [h1, ← mul_assoc, neg_one_pow_mul_self, one_mul]

end Cov

end ReciprocityTheory.ChartRestriction.DS.Lap.EvalC

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open Matrix ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap.EvalC

universe u

def CapelliCovStatement : Prop :=
  ∀ (𝒰 : Type u) [Ring 𝒰] [Algebra ℂ 𝒰] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → 𝒰)
    (g g' : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (x : ℂ), Capelli.GlRelR E → g * g' = 1 →
    ∀ d c : Fin (m + 1),
      ((-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
          Capelli.cminor (fun a b => ∑ c', ∑ d', (g c' a * g' b d') • E c' d') d.succAbove c.succAbove x =
        ∑ d', ∑ c', (g' d d' * g c' c * (-1 : ℂ) ^ ((d' : ℕ) + (c' : ℕ))) •
          Capelli.cminor E d'.succAbove c'.succAbove x

theorem capelliCov : CapelliCovStatement.{u} := by
  intro 𝒰 _ _ m E g g' x hE hgg' d c
  have hg'g : g' * g = 1 := mul_eq_one_comm.mp hgg'
  have hAB : gᵀ * g'ᵀ = 1 := by rw [← Matrix.transpose_mul, hg'g, Matrix.transpose_one]
  have hfam : (fun a b => ∑ c', ∑ d', (g c' a * g' b d') • E c' d') = frameAB gᵀ g'ᵀ E := rfl
  have hD : g.det * g'.det = 1 := by rw [← Matrix.det_mul, hgg', Matrix.det_one]
  rw [hfam, cminor_frameAB_minor E hE _ _ hAB d c x, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d' _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [smul_smul]
  congr 1
  have e1 : (gᵀ.submatrix d.succAbove d'.succAbove).det = (g.submatrix d'.succAbove d.succAbove).det := by
    rw [← Matrix.det_transpose]; rfl
  have e2 : (g'ᵀ.submatrix c'.succAbove c.succAbove).det = (g'.submatrix c.succAbove c'.succAbove).det := by
    rw [← Matrix.det_transpose]; rfl
  rw [e1, e2, det_sub_succAbove g g' hg'g, det_sub_succAbove g' g hgg']
  simp only [pow_add]
  linear_combination (g' d d' * g c' c * (-1 : ℂ) ^ (d' : ℕ) * (-1 : ℂ) ^ (c' : ℕ)) *
    (((-1 : ℂ) ^ (c : ℕ) * (-1 : ℂ) ^ (c : ℕ) * (g.det * g'.det)) * neg_one_pow_mul_self (d : ℕ) +
      (g.det * g'.det) * neg_one_pow_mul_self (c : ℕ) + hD)

section Frame

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem frameE_eq_frameAB {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ) (E : Fin n → Fin n → Module.End ℂ M) :
    frameE Q E = EvalC.frameAB (Q⁻¹)ᵀ Qᵀ E := rfl

theorem frameE_glRep {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ) (hQ : Q * Q⁻¹ = 1)
    (E : Fin n → Fin n → Module.End ℂ M) (hE : IsGlRep E) : IsGlRep (frameE Q E) := by
  rw [frameE_eq_frameAB]
  exact EvalC.frameAB_glRel _ _ (by rw [← Matrix.transpose_mul, hQ, Matrix.transpose_one]) E hE

theorem frameE_cov {m : ℕ} (Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) (hQ : Q⁻¹ * Q = 1)
    (E : Fin (m + 1) → Fin (m + 1) → Module.End ℂ M) (hE : IsGlRep E) (α γ : Fin (m + 1) → ℂ) (x : ℂ) :
    ∑ d : Fin (m + 1), ∑ c : Fin (m + 1), (α d * γ c * (-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
        Capelli.cminor (frameE Q E) d.succAbove c.succAbove x =
      ∑ d : Fin (m + 1), ∑ c : Fin (m + 1), ((Qᵀ *ᵥ α) d * (Q⁻¹ *ᵥ γ) c * (-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
        Capelli.cminor E d.succAbove c.succAbove x := by
  have hcov := capelliCov (Module.End ℂ M) m E Q⁻¹ Q x hE hQ
  have e : ∀ d c : Fin (m + 1), (α d * γ c * (-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
      Capelli.cminor (frameE Q E) d.succAbove c.succAbove x =
      (α d * γ c) • ∑ d' : Fin (m + 1), ∑ c' : Fin (m + 1),
        (Q d d' * Q⁻¹ c' c * (-1 : ℂ) ^ ((d' : ℕ) + (c' : ℕ))) • Capelli.cminor E d'.succAbove c'.succAbove x := by
    intro d c; rw [mul_smul, ← hcov d c]; rfl
  simp only [e, Finset.smul_sum, smul_smul]
  rw [EvalC.sum_four_swap_pairs_alt (fun d' c' d c => (α d * γ c * (Q d d' * Q⁻¹ c' c * (-1 : ℂ) ^ ((d' : ℕ) + (c' : ℕ)))) •
    Capelli.cminor E d'.succAbove c'.succAbove x)]
  refine Finset.sum_congr rfl fun d' _ => Finset.sum_congr rfl fun c' _ => ?_
  simp only [← Finset.sum_smul]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

end Frame

end ReciprocityTheory.ChartRestriction.DS.Lap
