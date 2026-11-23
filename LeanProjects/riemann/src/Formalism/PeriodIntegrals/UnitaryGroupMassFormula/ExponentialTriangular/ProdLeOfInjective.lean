import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.SortedSpec

open Matrix Finset

noncomputable section

namespace PI.ET

theorem det_mul_rect {R : Type*} [CommRing R] {k n : ℕ}
    (A : Matrix (Fin k) (Fin n) R) (B : Matrix (Fin n) (Fin k) R) :
    (A * B).det = ∑ f : Fin k → Fin n, (∏ i, B (f i) i) * (A.submatrix id f).det := by
  simp only [det_apply, mul_apply, Fintype.prod_sum, Finset.smul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [Finset.prod_mul_distrib, submatrix_apply, id, Units.smul_def, zsmul_eq_mul]
  ring

theorem sum_comp_perm {M : Type*} [AddCommMonoid M] {k n : ℕ} (F : (Fin k → Fin n) → M)
    (τ : Equiv.Perm (Fin k)) : ∑ f : Fin k → Fin n, F (fun i => f (τ i)) = ∑ f, F f := (Equiv.arrowCongr τ.symm (Equiv.refl (Fin n))).sum_comp F

theorem factorial_mul_det (k n : ℕ) (q : Fin n → ℂ) (V : Matrix (Fin n) (Fin k) ℂ) :
    (k.factorial : ℂ) * (Vᴴ * diagonal q * V).det =
      ∑ f : Fin k → Fin n, (∏ i, q (f i)) *
        ((V.submatrix f id).det * star (V.submatrix f id).det) := by
  have h2 : ∀ f : Fin k → Fin n, ((Vᴴ * diagonal q).submatrix id f).det =
      (∏ i, q (f i)) * star (V.submatrix f id).det := by
    intro f
    have he : (Vᴴ * diagonal q).submatrix id f = (V.submatrix f id)ᴴ * diagonal (fun i => q (f i)) := by
      ext a b
      simp [conjTranspose_apply, mul_diagonal, submatrix_apply]
    rw [he, det_mul, det_diagonal, det_conjTranspose, mul_comm]
  have h3 : ∀ (f : Fin k → Fin n) (τ : Equiv.Perm (Fin k)),
      (V.submatrix (fun i => f (τ i)) id).det = Equiv.Perm.sign τ * (V.submatrix f id).det := by
    intro f τ
    exact det_permute τ (V.submatrix f id)
  have hperm : ∀ τ : Equiv.Perm (Fin k),
      ∑ f : Fin k → Fin n, (∏ i, V (f i) i) * ((∏ i, q (f i)) * star (V.submatrix f id).det) =
        ∑ f : Fin k → Fin n, ((Equiv.Perm.sign τ : ℂ) * ∏ i, V (f (τ i)) i) *
          ((∏ i, q (f i)) * star (V.submatrix f id).det) := by
    intro τ
    rw [← sum_comp_perm (fun f : Fin k → Fin n =>
      (∏ i, V (f i) i) * ((∏ i, q (f i)) * star (V.submatrix f id).det)) τ]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only
    rw [h3 f τ, Equiv.prod_comp τ (fun i => q (f i)), star_mul', star_intCast]
    ring
  rw [det_mul_rect]
  simp_rw [h2]
  rw [show (k.factorial : ℂ) * ∑ f : Fin k → Fin n,
      (∏ i, V (f i) i) * ((∏ i, q (f i)) * star (V.submatrix f id).det) =
      ∑ τ : Equiv.Perm (Fin k), ∑ f : Fin k → Fin n,
      (∏ i, V (f i) i) * ((∏ i, q (f i)) * star (V.submatrix f id).det) by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]]
  rw [Finset.sum_congr rfl fun τ _ => hperm τ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hd : (V.submatrix f id).det = ∑ τ : Equiv.Perm (Fin k), (Equiv.Perm.sign τ : ℂ) * ∏ i, V (f (τ i)) i := by
    rw [det_apply']
    rfl
  rw [← Finset.sum_mul, ← hd]
  ring

theorem prod_le_of_injective {n k : ℕ} (hk : k ≤ n) (p : Fin n → ℝ) (hp : Antitone p)
    (hpos : ∀ i, 0 ≤ p i) (f : Fin k → Fin n) (hf : Function.Injective f) :
    ∏ i, p (f i) ≤ ∏ i : Fin k, p (Fin.castLE hk i) := by
  classical
  have hs : (Finset.univ.image f).card = k := by
    rw [Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  set e := (Finset.univ.image f).orderEmbOfFin hs with he
  have h1 : ∏ i, p (f i) = ∏ j : Fin k, p (e j) := by
    rw [← Finset.prod_image (fun i _ j _ h => hf h), ← Finset.map_orderEmbOfFin_univ _ hs,
      Finset.prod_map]
    rfl
  have h3 : ∀ m (hm : m < k), m ≤ (e ⟨m, hm⟩ : ℕ) := by
    intro m
    induction m with
    | zero => intro _; exact Nat.zero_le _
    | succ m ih =>
      intro hm
      have hlt : e ⟨m, by omega⟩ < e ⟨m + 1, hm⟩ := e.strictMono (Fin.mk_lt_mk.2 (Nat.lt_succ_self m))
      have h' : (e ⟨m, by omega⟩ : ℕ) < e ⟨m + 1, hm⟩ := hlt
      have := ih (by omega)
      omega
  rw [h1]
  refine Finset.prod_le_prod (fun j _ => hpos _) fun j _ => hp ?_
  rw [Fin.le_iff_val_le_val, Fin.val_castLE]
  exact h3 j.1 j.2

theorem kyFan_diag {n k : ℕ} (hk : k ≤ n) (p : Fin n → ℝ) (hp : Antitone p)
    (hpos : ∀ i, 0 < p i) (V : Matrix (Fin n) (Fin k) ℂ) (hV : Vᴴ * V = 1) :
    ‖(Vᴴ * diagonal (fun i => (p i : ℂ)) * V).det‖ ≤ ∏ i : Fin k, p (Fin.castLE hk i) := by
  have hT := factorial_mul_det k n (fun i => (p i : ℂ)) V
  have hU := factorial_mul_det k n (fun _ => (1 : ℂ)) V
  rw [diagonal_one, Matrix.mul_one, hV, det_one, mul_one] at hU
  simp only [Finset.prod_const_one, one_mul] at hU
  have hsq : ∀ f : Fin k → Fin n, (V.submatrix f id).det * star (V.submatrix f id).det =
      ((‖(V.submatrix f id).det‖ ^ 2 : ℝ) : ℂ) := by
    intro f
    rw [Complex.star_def, Complex.mul_conj']
    push_cast
    rfl
  simp_rw [hsq] at hU
  have hU' : (k.factorial : ℝ) = ∑ f : Fin k → Fin n, ‖(V.submatrix f id).det‖ ^ 2 := by
    exact_mod_cast hU
  set P := ∏ i : Fin k, p (Fin.castLE hk i)
  have hterm : ∀ f : Fin k → Fin n,
      ‖(∏ i, ((p (f i) : ℝ) : ℂ)) * ((V.submatrix f id).det * star (V.submatrix f id).det)‖ ≤
        P * ‖(V.submatrix f id).det‖ ^ 2 := by
    intro f
    rw [hsq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _), norm_prod]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos _)]
    by_cases hf : Function.Injective f
    · exact mul_le_mul_of_nonneg_right (prod_le_of_injective hk p hp (fun i => (hpos i).le) f hf)
        (sq_nonneg _)
    · obtain ⟨i, j, hij, hne⟩ : ∃ i j, f i = f j ∧ i ≠ j := by
        by_contra hc
        exact hf fun i j h => by_contra fun hne => hc ⟨i, j, h, hne⟩
      have h0 : (V.submatrix f id).det = 0 := det_zero_of_row_eq hne (by ext c; simp [hij])
      simp [h0]
  have hfact : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hmain : (k.factorial : ℝ) * ‖(Vᴴ * diagonal (fun i => (p i : ℂ)) * V).det‖ ≤ P * k.factorial := by
    calc (k.factorial : ℝ) * ‖(Vᴴ * diagonal (fun i => (p i : ℂ)) * V).det‖
        = ‖(k.factorial : ℂ) * (Vᴴ * diagonal (fun i => (p i : ℂ)) * V).det‖ := by
          rw [norm_mul, Complex.norm_natCast]
      _ = ‖∑ f : Fin k → Fin n, (∏ i, ((p (f i) : ℝ) : ℂ)) *
          ((V.submatrix f id).det * star (V.submatrix f id).det)‖ := by rw [hT]
      _ ≤ ∑ f : Fin k → Fin n, ‖(∏ i, ((p (f i) : ℝ) : ℂ)) *
          ((V.submatrix f id).det * star (V.submatrix f id).det)‖ := norm_sum_le _ _
      _ ≤ ∑ f : Fin k → Fin n, P * ‖(V.submatrix f id).det‖ ^ 2 := Finset.sum_le_sum fun f _ => hterm f
      _ = P * k.factorial := by rw [← Finset.mul_sum, hU']
  nlinarith [norm_nonneg (Vᴴ * diagonal (fun i => (p i : ℂ)) * V).det]

theorem kyFanDet : KyFanDet := by
  intro n k hk p W V hp hpos hW hV
  have hW1 : Wᴴ * W = 1 := by
    have := (mem_unitaryGroup_iff').1 hW
    rwa [star_eq_conjTranspose] at this
  have hW2 : W * Wᴴ = 1 := by
    have := (mem_unitaryGroup_iff).1 hW
    rwa [star_eq_conjTranspose] at this
  have e1 : Vᴴ * (W * diagonal (fun i => (p i : ℂ)) * Wᴴ) * V =
      (Wᴴ * V)ᴴ * diagonal (fun i => (p i : ℂ)) * (Wᴴ * V) := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  have e2 : (Wᴴ * V)ᴴ * (Wᴴ * V) = 1 := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc W,
      hW2, Matrix.one_mul, hV]
  rw [e1]
  exact kyFan_diag hk p hp hpos (Wᴴ * V) e2

end PI.ET
