import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageMapLatticeEquivStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric

namespace GlobalTheory.CuspGeneric

namespace MirCol

section ColAct

variable {R : Type} [CommRing R] {a k : ℕ}

def colAct (M : Matrix (Fin a) (Fin a) R) (x : UnipotentBlockColumnIndex a k k → R) : UnipotentBlockColumnIndex a k k → R :=
  fun t => ∑ s, M t.1.1 s.1.1 * x s

theorem posM_col_apply (x : UnipotentBlockColumnIndex a k k → R) (t : UnipotentBlockColumnIndex a k k) :
    posM (Subtype.val : UnipotentBlockColumnIndex a k k → Fin a × Fin a) x t.1.1 t.1.2 = x t := by
  simp only [posM, Matrix.sum_apply, Matrix.single_apply]
  rw [Finset.sum_eq_single t]
  · simp
  · intro s _ hne
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hne (Subtype.ext (Prod.ext h1 h2))
  · simp

theorem posM_col_mul (M : Matrix (Fin a) (Fin a) R)
    (hM : ∀ i l : Fin a, k ≤ (i : ℕ) → M i l = (1 : Matrix (Fin a) (Fin a) R) i l) (x : UnipotentBlockColumnIndex a k k → R) :
    posM (Subtype.val : UnipotentBlockColumnIndex a k k → Fin a × Fin a) x * M = posM Subtype.val x := by
  simp only [posM, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single t.1.2]
  · rw [hM _ _ t.2.2.1]
    simp only [Matrix.single_apply, Matrix.one_apply]
    by_cases h1 : t.1.1 = i <;> by_cases h2 : t.1.2 = j <;> simp [h1, h2]
  · intro l _ hl
    rw [Matrix.single_apply, if_neg (fun h => hl h.2.symm), zero_mul]
  · simp

theorem mul_posM_col (M : Matrix (Fin a) (Fin a) R)
    (hM : ∀ i l : Fin a, k ≤ (i : ℕ) → M i l = (1 : Matrix (Fin a) (Fin a) R) i l) (x : UnipotentBlockColumnIndex a k k → R) :
    M * posM (Subtype.val : UnipotentBlockColumnIndex a k k → Fin a × Fin a) x = posM Subtype.val (colAct M x) := by
  ext i j
  have hL : (M * posM (Subtype.val : UnipotentBlockColumnIndex a k k → Fin a × Fin a) x) i j =
      ∑ s : UnipotentBlockColumnIndex a k k, if s.1.2 = j then M i s.1.1 * x s else 0 := by
    simp only [Matrix.mul_apply, posM, Matrix.sum_apply, Matrix.single_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_eq_single s.1.1]
    · simp
    · intro l _ hl
      rw [if_neg (fun h => hl h.1.symm), mul_zero]
    · simp
  rw [hL]
  simp only [posM, Matrix.sum_apply, Matrix.single_apply]
  by_cases hi : (i : ℕ) < k
  · by_cases hj : (j : ℕ) = k
    · symm
      rw [Finset.sum_eq_single (⟨(i, j), hi, hj.ge, hj.le⟩ : UnipotentBlockColumnIndex a k k)]
      · rw [if_pos (And.intro rfl rfl)]
        simp only [colAct]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [if_pos]
        have h1 := s.2.2
        exact Fin.ext (by omega)
      · intro t _ hne
        rw [if_neg]
        rintro ⟨h1, h2⟩
        exact hne (Subtype.ext (Prod.ext h1 h2))
      · simp
    · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
      · intro t _
        rw [if_neg]
        rintro ⟨_, h2⟩
        have h1 := t.2.2
        rw [← h2] at hj
        omega
      · intro t _
        rw [if_neg]
        intro h2
        have h1 := t.2.2
        rw [← h2] at hj
        omega
  · rw [Finset.sum_eq_zero, Finset.sum_eq_zero]
    · intro t _
      rw [if_neg]
      rintro ⟨h1, _⟩
      have h2 := t.2.1
      rw [h1] at h2
      exact hi h2
    · intro s _
      have h2 := s.2.1
      rw [hM i _ (by omega), Matrix.one_apply_ne (fun h => by rw [h] at hi; exact hi h2)]
      simp

theorem colAct_colAct {M N : Matrix (Fin a) (Fin a) R}
    (hM : ∀ i l : Fin a, k ≤ (i : ℕ) → M i l = (1 : Matrix (Fin a) (Fin a) R) i l)
    (hN : ∀ i l : Fin a, k ≤ (i : ℕ) → N i l = (1 : Matrix (Fin a) (Fin a) R) i l)
    (h : M * N = 1) (x : UnipotentBlockColumnIndex a k k → R) : colAct M (colAct N x) = x := by
  funext t
  rw [← posM_col_apply (colAct M (colAct N x)) t, ← mul_posM_col M hM, ← mul_posM_col N hN, ← Matrix.mul_assoc, h,
    Matrix.one_mul, posM_col_apply]

theorem inv_rows (γ : GL (Fin a) R)
    (hγ : ∀ i l : Fin a, k ≤ (i : ℕ) → γ.val i l = (1 : Matrix (Fin a) (Fin a) R) i l) :
    ∀ i l : Fin a, k ≤ (i : ℕ) → (γ⁻¹).val i l = (1 : Matrix (Fin a) (Fin a) R) i l := by
  intro i l hi
  have h : γ.val * (γ⁻¹).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 := congrFun (congrFun h i) l
  rw [Matrix.mul_apply] at h2
  simp only [hγ i _ hi, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h2
  simpa [Matrix.one_apply] using h2

theorem blkU_mul (γ : GL (Fin a) R)
    (hγ : ∀ i l : Fin a, k ≤ (i : ℕ) → γ.val i l = (1 : Matrix (Fin a) (Fin a) R) i l) (x : UnipotentBlockColumnIndex a k k → R) :
    blkU x * γ = γ * blkU (colAct (γ⁻¹).val x) := by
  apply Units.ext
  change (1 + posM Subtype.val x) * γ.val = γ.val * (1 + posM Subtype.val (colAct (γ⁻¹).val x))
  have h : γ.val * (γ⁻¹).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [← mul_posM_col _ (inv_rows γ hγ), add_mul, mul_add, posM_col_mul _ hγ, ← Matrix.mul_assoc, h]
  simp

end ColAct

section Rat

variable {E : Type} [Field E] [NumberField E] {a k : ℕ}

theorem ratGL_val_apply (γ : GL (Fin a) E) (i l : Fin a) :
    (ratGL E a γ).val i l = algebraMap E (Ad E) (γ.val i l) := rfl

theorem ratGL_rows (γ : GL (Fin a) E)
    (hγ : ∀ i l : Fin a, k ≤ (i : ℕ) → γ.val i l = (1 : Matrix (Fin a) (Fin a) E) i l) :
    ∀ i l : Fin a, k ≤ (i : ℕ) → (ratGL E a γ).val i l = (1 : Matrix (Fin a) (Fin a) (Ad E)) i l := by
  intro i l hi
  rw [ratGL_val_apply, hγ i l hi, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem colAct_rat (γ : GL (Fin a) E) (c : UnipotentBlockColumnIndex a k k → E) :
    colAct (ratGL E a γ).val (fun t => algebraMap E (Ad E) (c t)) =
      fun t => algebraMap E (Ad E) (colAct γ.val c t) := by
  funext t
  simp only [colAct, ratGL_val_apply, map_sum, map_mul]

theorem continuous_colAct (M : Matrix (Fin a) (Fin a) (Ad E)) :
    Continuous (colAct M : (UnipotentBlockColumnIndex a k k → Ad E) → UnipotentBlockColumnIndex a k k → Ad E) :=
  continuous_pi fun _ => continuous_finset_sum _ fun s _ => continuous_const.mul (continuous_apply s)

def colEquiv (γ : GL (Fin a) E)
    (hγ : ∀ i l : Fin a, k ≤ (i : ℕ) → γ.val i l = (1 : Matrix (Fin a) (Fin a) E) i l) :
    (UnipotentBlockColumnIndex a k k → Ad E) ≃ₜ+ (UnipotentBlockColumnIndex a k k → Ad E) where
  toFun := colAct (ratGL E a γ).val
  invFun := colAct (ratGL E a γ⁻¹).val
  left_inv x := colAct_colAct (ratGL_rows _ (inv_rows γ hγ)) (ratGL_rows _ hγ)
    (by rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]) x
  right_inv x := colAct_colAct (ratGL_rows _ hγ) (ratGL_rows _ (inv_rows γ hγ))
    (by rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]) x
  map_add' x y := by
    funext t
    simp only [colAct, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  continuous_toFun := continuous_colAct _
  continuous_invFun := continuous_colAct _

theorem colEquiv_mem (γ : GL (Fin a) E)
    (hγ : ∀ i l : Fin a, k ≤ (i : ℕ) → γ.val i l = (1 : Matrix (Fin a) (Fin a) E) i l)
    (x : UnipotentBlockColumnIndex a k k → Ad E) : colAct (ratGL E a γ).val x ∈ ratV E (UnipotentBlockColumnIndex a k k) ↔ x ∈ ratV E (UnipotentBlockColumnIndex a k k) := by
  have key : ∀ (δ : GL (Fin a) E) (y : UnipotentBlockColumnIndex a k k → Ad E), y ∈ ratV E (UnipotentBlockColumnIndex a k k) →
      colAct (ratGL E a δ).val y ∈ ratV E (UnipotentBlockColumnIndex a k k) := by
    rintro δ _ ⟨c, rfl⟩
    exact ⟨colAct δ.val c, (colAct_rat δ c).symm⟩
  refine ⟨fun h => ?_, key γ x⟩
  have h2 := key γ⁻¹ _ h
  rwa [colAct_colAct (ratGL_rows _ (inv_rows γ hγ)) (ratGL_rows _ hγ)
    (by rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one])] at h2

theorem dot_colAct (γ : GL (Fin a) E) (ξ : UnipotentBlockColumnIndex a k k → E) (y : UnipotentBlockColumnIndex a k k → Ad E) :
    dot ξ (colAct (ratGL E a γ).val y) = dot (fun t => ∑ s : UnipotentBlockColumnIndex a k k, ξ s * γ.val s.1.1 t.1.1) y := by
  simp only [dot, colAct, ratGL_val_apply, Finset.mul_sum, map_sum, Finset.sum_mul, map_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

end Rat

end MirCol

open MirCol

theorem coefF_ratGL_mul : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ψ : AddChar (Ad E) ℂ), StdPsi ψ → ∀ (m : ℕ)
    (f : GA E a → ℂ), Continuous f → (∀ γ : GL (Fin a) E, IsMir (m + 1) γ → ∀ g, f (ratGL E a γ * g) = f g) →
    ∀ γ : GL (Fin a) E, IsMir (m + 1) γ → ∀ (ξ : UnipotentBlockColumnIndex a (m + 1) (m + 1) → E) (g : GA E a),
    coefF ψ (m + 1) ξ f (ratGL E a γ * g) =
      coefF ψ (m + 1) (fun t => ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), ξ s * γ.val s.1.1 t.1.1) f g := by
  intro E _ _ a ψ hψ m f hf hl γ hγ ξ g
  have hr : ∀ i l : Fin a, m + 1 ≤ (i : ℕ) → γ.val i l = (1 : Matrix (Fin a) (Fin a) E) i l :=
    fun i l h => hγ i l (Or.inl h)
  have hri := inv_rows γ hr
  have hper := per_coef hψ (fun t => ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), ξ s * γ.val s.1.1 t.1.1) hf
    (fun c g => hl _ (isMir_blkU c) g) g
  have hmem : ∀ x : UnipotentBlockColumnIndex a (m + 1) (m + 1) → Ad E,
      colEquiv γ⁻¹ hri x ∈ ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1)) ↔ x ∈ ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1)) :=
    fun x => colEquiv_mem γ⁻¹ hri x
  have key := GlobalTheory.T.quotientAverage_map_lattice_equiv _ _ (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1))) (ratV E (UnipotentBlockColumnIndex a (m + 1) (m + 1)))
    (isCoLat_ratV E _) (isCoLat_ratV E _) (colEquiv γ⁻¹ hri) hmem _ hper
  change avg _ _ = avg _ _
  rw [← key]
  congr 1
  funext x
  have hx : colAct (ratGL E a γ).val (colEquiv γ⁻¹ hri x) = x :=
    colAct_colAct (ratGL_rows _ hr) (ratGL_rows _ hri)
      (by rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]) x
  have hd : dot (fun t => ∑ s : UnipotentBlockColumnIndex a (m + 1) (m + 1), ξ s * γ.val s.1.1 t.1.1) (colEquiv γ⁻¹ hri x) = dot ξ x := by
    rw [← dot_colAct, hx]
  have hu : blkU x * (ratGL E a γ * g) = ratGL E a γ * (blkU (colEquiv γ⁻¹ hri x) * g) := by
    rw [← mul_assoc, blkU_mul (ratGL E a γ) (ratGL_rows _ hr), mul_assoc, ← map_inv]
    rfl
  beta_reduce
  rw [hd, hu, hl γ hγ]

end GlobalTheory.CuspGeneric
