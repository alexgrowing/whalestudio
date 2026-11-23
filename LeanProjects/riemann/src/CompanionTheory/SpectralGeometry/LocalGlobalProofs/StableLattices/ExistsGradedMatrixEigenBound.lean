import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HsConjTranspose
open Matrix
open CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.L ReciprocityTheory.ChartRestriction.DS GlobalTheory.CompanionTheory.PSubFlag GlobalTheory.CompanionTheory.UGeo

noncomputable section

namespace GlobalTheory.CompanionTheory.UGeo.SpecGrad

variable {n : ℕ}

theorem aeval_intertwine {R : Type*} [Ring R] [Algebra ℝ R] {X A B : R} (h : X * A = B * X)
    (p : Polynomial ℝ) : X * Polynomial.aeval A p = Polynomial.aeval B p * X := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, mul_add, add_mul, hp, hq]
  | monomial k a =>
    have hk : X * A ^ k = B ^ k * X := by
      induction k with
      | zero => simp
      | succ k ih => rw [pow_succ, ← mul_assoc, ih, mul_assoc, h, ← mul_assoc, ← pow_succ]
    simp only [Polynomial.aeval_monomial]
    rw [← mul_assoc, ← Algebra.commutes, mul_assoc, hk, mul_assoc]

def cj (U : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  U * diagonal (fun i => (d i : ℂ)) * Uᴴ

variable {U : Matrix (Fin n) (Fin n) ℂ}

theorem cj_mul (h1 : Uᴴ * U = 1) (d e : Fin n → ℝ) : cj U d * cj U e = cj U (fun i => d i * e i) := by
  have hd : diagonal (fun i => (d i : ℂ)) * diagonal (fun i => (e i : ℂ))
      = diagonal (fun i => ((d i * e i : ℝ) : ℂ)) := by
    rw [diagonal_mul_diagonal]; simp
  simp only [cj]
  calc _ = U * diagonal (fun i => (d i : ℂ)) * (Uᴴ * U) * diagonal (fun i => (e i : ℂ)) * Uᴴ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, Matrix.mul_one, Matrix.mul_assoc U, hd]

theorem cj_conj (d : Fin n → ℝ) : (cj U d)ᴴ = cj U d := by
  have h : (diagonal fun i => (d i : ℂ))ᴴ = diagonal fun i => (d i : ℂ) := by
    rw [diagonal_conjTranspose]; congr 1; funext i; simp
  rw [cj, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, h, Matrix.mul_assoc]

theorem cj_one (h2 : U * Uᴴ = 1) : cj U (fun _ => 1) = 1 := by
  simp [cj, h2]

theorem cj_add (d e : Fin n → ℝ) : cj U (fun i => d i + e i) = cj U d + cj U e := by
  rw [cj, cj, cj, ← Matrix.add_mul, ← Matrix.mul_add, diagonal_add]
  congr 3; funext i; push_cast; rfl

theorem cj_smul (c : ℝ) (d : Fin n → ℝ) : cj U (fun i => c * d i) = (c : ℂ) • cj U d := by
  have h : (diagonal fun i => ((c * d i : ℝ) : ℂ)) = (c : ℂ) • diagonal fun i => (d i : ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [diagonal_apply_ne _ hij]
  rw [cj, cj, h, Matrix.mul_smul, Matrix.smul_mul]

theorem cj_neg (d : Fin n → ℝ) : cj U (fun i => - d i) = - cj U d := by
  have := cj_smul (U := U) (-1) d
  simpa using this

theorem algebraMap_eq (a : ℝ) : algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ) a = (a : ℂ) • 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [Matrix.algebraMap_matrix_apply]
  · simp [Matrix.algebraMap_matrix_apply, hij]

theorem cj_aeval (h1 : Uᴴ * U = 1) (h2 : U * Uᴴ = 1) (d : Fin n → ℝ) (p : Polynomial ℝ) :
    Polynomial.aeval (cj U d) p = cj U (fun i => p.eval (d i)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq, cj_add]
  | monomial k a =>
    have hk : cj U d ^ k = cj U (fun i => d i ^ k) := by
      induction k with
      | zero => simp only [pow_zero]; exact (cj_one h2).symm
      | succ k ih => rw [pow_succ, ih, cj_mul h1]; simp only [pow_succ]
    rw [Polynomial.aeval_monomial, hk, algebraMap_eq, smul_mul_assoc, one_mul, ← cj_smul]
    simp only [Polynomial.eval_monomial]

theorem cj_eq_zero (h1 : Uᴴ * U = 1) {d : Fin n → ℝ} (h : cj U d = 0) (i : Fin n) : d i = 0 := by
  have e : diagonal (fun i => (d i : ℂ)) = Uᴴ * cj U d * U := by
    simp only [cj]
    calc _ = (Uᴴ * U) * diagonal (fun i => (d i : ℂ)) * (Uᴴ * U) := by rw [h1]; simp
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [h] at e
  have := congrFun (congrFun e i) i
  simpa using this

theorem nsq_eq_dot (v : Fin n → ℂ) : ((nsq v : ℝ) : ℂ) = star v ⬝ᵥ v := by
  simp only [nsq, dotProduct, Pi.star_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, Complex.conj_mul']
  push_cast; rfl

theorem nsq_eq_of_gram {M N : Matrix (Fin n) (Fin n) ℂ} (h : Mᴴ * M = Nᴴ * N) (y : Fin n → ℂ) :
    nsq (M *ᵥ y) = nsq (N *ᵥ y) := by
  have key : ∀ M : Matrix (Fin n) (Fin n) ℂ, ((nsq (M *ᵥ y) : ℝ) : ℂ) = star y ⬝ᵥ ((Mᴴ * M) *ᵥ y) := by
    intro M
    rw [nsq_eq_dot, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]
  exact Complex.ofReal_injective (by rw [key, key, h])

theorem nsq_cj (h1 : Uᴴ * U = 1) (d : Fin n → ℝ) (y : Fin n → ℂ) :
    nsq (cj U d *ᵥ y) = ∑ i, d i ^ 2 * ‖(Uᴴ *ᵥ y) i‖ ^ 2 := by
  have hU : ∀ w : Fin n → ℂ, nsq (U *ᵥ w) = nsq w := fun w => by
    have := nsq_eq_of_gram (M := U) (N := 1) (by simp [h1]) w
    simpa using this
  have e : cj U d *ᵥ y = U *ᵥ (diagonal (fun i => (d i : ℂ)) *ᵥ (Uᴴ *ᵥ y)) := by
    simp only [cj, mulVec_mulVec, Matrix.mul_assoc]
  rw [e, hU]
  simp only [nsq, mulVec_diagonal, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem core {J G H : Matrix (Fin n) (Fin n) ℂ} (hJ : J * J = 1) (hHG : H * G = 1) (hGH : G * H = 1)
    (hJc : Jᴴ = J) (hHJ : H = J * Gᴴ * J) (hT : (Hᴴ * H).IsHermitian) (f : ℝ → ℝ) (α β : ℝ)
    (hf : ∀ l : ℝ, 0 < l → (f l = -1 ∨ f l = 0 ∨ f l = 1) ∧ f l⁻¹ = - f l)
    (hα : ∀ i, f (hT.eigenvalues i) = -1 → α ≤ hT.eigenvalues i)
    (hβ : ∀ i, f (hT.eigenvalues i) = 0 → β⁻¹ ≤ hT.eigenvalues i)
    (hne : ∃ i, f (hT.eigenvalues i) ≠ 0) :
    ∃ A : Matrix (Fin n) (Fin n) ℂ, Aᴴ = A ∧ A * A * A = A ∧ A ≠ 0 ∧ J * A = -A * J ∧
      ∀ y : Fin n → ℂ, α * nsq (Pm A *ᵥ y) + β⁻¹ * nsq (Pz A *ᵥ y) ≤ nsq (H *ᵥ y) := by
  obtain ⟨U, hUdef⟩ : ∃ U : Matrix (Fin n) (Fin n) ℂ, U = (hT.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) :=
    ⟨_, rfl⟩
  have h1 : Uᴴ * U = 1 := by
    rw [hUdef]; exact Matrix.mem_unitaryGroup_iff'.1 hT.eigenvectorUnitary.2
  have h2 : U * Uᴴ = 1 := by
    rw [hUdef]; exact Matrix.mem_unitaryGroup_iff.1 hT.eigenvectorUnitary.2
  obtain ⟨lam, hlam⟩ : ∃ lam : Fin n → ℝ, lam = hT.eigenvalues := ⟨_, rfl⟩
  rw [← hlam] at hα hβ hne
  have hTc : Hᴴ * H = cj U lam := by
    have := hT.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply, ← hUdef, ← hlam, Matrix.star_eq_conjTranspose] at this
    exact this
  have hTG : (Hᴴ * H) * (G * Gᴴ) = 1 := by
    calc _ = Hᴴ * (H * G) * Gᴴ := by simp only [Matrix.mul_assoc]
      _ = (G * H)ᴴ := by rw [hHG, Matrix.mul_one, conjTranspose_mul]
      _ = 1 := by rw [hGH, conjTranspose_one]
  have hnn : ∀ i, 0 ≤ lam i := fun i => by
    rw [hlam]
    open scoped ComplexOrder in
    exact (Matrix.posSemidef_conjTranspose_mul_self H).eigenvalues_nonneg i
  have hn0 : ∀ i, lam i ≠ 0 := fun i h0 => by
    have hd := congrArg Matrix.det hTG
    rw [Matrix.det_mul, hT.det_eq_prod_eigenvalues, ← hlam, Finset.prod_eq_zero (Finset.mem_univ i) (by simp [h0])] at hd
    simp at hd
  have hpos : ∀ i, 0 < lam i := fun i => lt_of_le_of_ne (hnn i) (hn0 i).symm
  have hinv : cj U (fun i => (lam i)⁻¹) = G * Gᴴ := by
    have e : cj U (fun i => (lam i)⁻¹) * (Hᴴ * H) = 1 := by
      rw [hTc, cj_mul h1, ← cj_one (U := U) h2]
      congr 1; funext i; exact inv_mul_cancel₀ (hn0 i)
    calc _ = cj U (fun i => (lam i)⁻¹) * ((Hᴴ * H) * (G * Gᴴ)) := by rw [hTG, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, e, Matrix.one_mul]
  have hHc : Hᴴ = J * G * J := by
    rw [hHJ]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hJc, Matrix.mul_assoc]
  have hJT : J * (Hᴴ * H) = (G * Gᴴ) * J := by
    rw [hHc, hHJ]
    calc _ = (J * J) * G * (J * J) * Gᴴ * J := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hJ, Matrix.one_mul, Matrix.mul_one]

  let S : Finset ℝ := Finset.univ.image lam ∪ Finset.univ.image (fun i => (lam i)⁻¹)
  let p : Polynomial ℝ := Lagrange.interpolate S id f
  have hp : ∀ x ∈ S, p.eval x = f x := fun x hx =>
    Lagrange.eval_interpolate_at_node (s := S) (v := id) f (Function.injective_id.injOn) hx
  have hp1 : ∀ i, p.eval (lam i) = f (lam i) := fun i =>
    hp _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  have hp2 : ∀ i, p.eval (lam i)⁻¹ = - f (lam i) := fun i => by
    rw [hp _ (Finset.mem_union_right _ (Finset.mem_image_of_mem (fun i => (lam i)⁻¹) (Finset.mem_univ i)))]
    exact (hf _ (hpos i)).2
  obtain ⟨a, ha⟩ : ∃ a : Fin n → ℝ, a = fun i => f (lam i) := ⟨_, rfl⟩
  have ha3 : ∀ i, a i = -1 ∨ a i = 0 ∨ a i = 1 := fun i => by
    rw [ha]; exact (hf _ (hpos i)).1
  have hA : Polynomial.aeval (Hᴴ * H) p = cj U a := by
    rw [hTc, cj_aeval h1 h2, ha]; congr 1; funext i; exact hp1 i
  have hAi : Polynomial.aeval (G * Gᴴ) p = - cj U a := by
    rw [← hinv, cj_aeval h1 h2, ← cj_neg, ha]; congr 1; funext i; exact hp2 i
  have hPm : Pm (cj U a) = cj U (fun i => (1 / 2 : ℝ) * (a i * a i + - a i)) := by
    rw [cj_smul, cj_add, cj_neg, ← cj_mul h1, ← sub_eq_add_neg]
    simp only [Pm]
    congr 1
    push_cast; rfl
  have hPz : Pz (cj U a) = cj U (fun i => 1 + - (a i * a i)) := by
    rw [cj_add, cj_neg, ← cj_mul h1, cj_one h2, ← sub_eq_add_neg]
    rfl
  refine ⟨cj U a, cj_conj a, ?_, ?_, ?_, ?_⟩
  · rw [cj_mul h1, cj_mul h1]
    congr 1; funext i
    rcases ha3 i with h | h | h <;> rw [h] <;> norm_num
  · intro h0
    obtain ⟨i, hi⟩ := hne
    exact hi (by have := cj_eq_zero h1 h0 i; rwa [ha] at this)
  · have := aeval_intertwine hJT p
    rwa [hA, hAi] at this
  · intro y
    have hH : nsq (H *ᵥ y) = nsq (cj U (fun i => Real.sqrt (lam i)) *ᵥ y) := by
      refine nsq_eq_of_gram ?_ y
      rw [cj_conj, cj_mul h1, hTc]
      congr 1; funext i; exact (Real.mul_self_sqrt (hnn i)).symm
    rw [hPm, hPz, hH, nsq_cj h1, nsq_cj h1, nsq_cj h1, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    have hc : 0 ≤ ‖(Uᴴ *ᵥ y) i‖ ^ 2 := by positivity
    rw [Real.sq_sqrt (hnn i)]
    have hfa : a i = f (lam i) := by rw [ha]
    rcases ha3 i with h | h | h
    · have h' := hα i (by rw [← hfa, h])
      rw [h]
      nlinarith
    · have h' := hβ i (by rw [← hfa, h])
      rw [h]
      nlinarith
    · rw [h]
      have := hpos i
      have h3 : 0 ≤ lam i * ‖(Uᴴ *ᵥ y) i‖ ^ 2 := by positivity
      nlinarith

end GlobalTheory.CompanionTheory.UGeo.SpecGrad

open GlobalTheory.CompanionTheory.UGeo.SpecGrad in

theorem GlobalTheory.CompanionTheory.UGeo.SpecGrad.grading_of_spectral :
    ∀ (n : ℕ) (ε : Fin n → Bool) (g : S7.UJ ε) (hT : ((S7.toM g⁻¹)ᴴ * S7.toM g⁻¹).IsHermitian) (f : ℝ → ℝ) (α β : ℝ), (∀ l : ℝ, 0 < l → (f l = -1 ∨ f l = 0 ∨ f l = 1) ∧ f l⁻¹ = - f l) → (∀ i, f (hT.eigenvalues i) = -1 → α ≤ hT.eigenvalues i) → (∀ i, f (hT.eigenvalues i) = 0 → β⁻¹ ≤ hT.eigenvalues i) → (∃ i, f (hT.eigenvalues i) ≠ 0) → ∃ A' : Matrix (Fin n) (Fin n) ℂ, IsGrad ε A' ∧ ∀ y : Fin n → ℂ, α * nsq (Pm A' *ᵥ y) + β⁻¹ * nsq (Pz A' *ᵥ y) ≤ nsq (S7.toM g⁻¹ *ᵥ y) := by
  intro n ε g hT f α β hf hα hβ hne
  have hHG : S7.toM g⁻¹ * S7.toM g = 1 := by
    show ((g⁻¹ : S7.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ).val * ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)).val = 1
    simp
  have hGH : S7.toM g * S7.toM g⁻¹ = 1 := by
    show ((g : (Matrix (Fin n) (Fin n) ℂ)ˣ)).val * ((g⁻¹ : S7.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ).val = 1
    simp
  obtain ⟨A, hc, h3, h0, hJ, hy⟩ := core (J := Formalism.REAL.Jm ε) (Formalism.REAL.Jm_mul_self ε) hHG hGH
    (Formalism.REAL.Jm_conjTranspose ε) (S7.toM_inv ε g) hT f α β hf hα hβ hne
  refine ⟨A, ⟨?_, hc, h3, h0⟩, hy⟩
  show Aᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * A = 0
  rw [hc, hJ, Matrix.neg_mul, add_neg_cancel]
