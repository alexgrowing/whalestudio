import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.NegBound

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section
namespace PI.FrameInd.UPosW

def cols (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) :
    Matrix (Fin (2 * r + k + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) ℂ :=
  Matrix.of fun p j => gramVec k r z z' γ j p

lemma cols_conjTranspose (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) :
    (cols k r z z' γ)ᴴ = Matrix.of fun i j => star (gramVec k r z z' γ i j) := by
  ext i j
  simp only [cols, Matrix.conjTranspose_apply, Matrix.of_apply]

lemma gram_eq (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) :
    (cols k r z z' γ)ᴴ * Hpk k r * cols k r z z' γ = gramM k r z z' γ := by
  ext i j
  rw [cols_conjTranspose]
  simp only [Matrix.mul_apply, Matrix.of_apply, cols, gramM, herm, dotProduct, Matrix.mulVec,
    Finset.sum_mul, Finset.mul_sum, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

lemma herm_cols (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r)
    (c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) :
    herm (Hpk k r) (cols k r z z' γ *ᵥ c) (cols k r z z' γ *ᵥ c) = star c ⬝ᵥ (gramM k r z z' γ *ᵥ c) := by
  rw [← gram_eq]
  simp only [herm, Matrix.star_mulVec]
  rw [← Matrix.dotProduct_mulVec]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

lemma herm_perp (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r)
    (v : Fin (2 * r + k + 1) → ℂ) (hv : v ∈ Uperp k r z z' γ) (c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) :
    herm (Hpk k r) v (cols k r z z' γ *ᵥ c) = 0 := by
  have h0 : ((cols k r z z' γ)ᴴ * Hpk k r) *ᵥ v = 0 := by
    have h := hv
    simp only [Uperp, LinearMap.mem_ker, Matrix.mulVecLin_apply] at h
    rw [cols_conjTranspose]
    exact h
  simp only [herm, Matrix.star_mulVec]
  rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, h0, dotProduct_zero]

lemma herm_perp' (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r)
    (v : Fin (2 * r + k + 1) → ℂ) (hv : v ∈ Uperp k r z z' γ) (c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) :
    herm (Hpk k r) (cols k r z z' γ *ᵥ c) v = 0 := by
  rw [ggHerm_swap _ (Formalism.QuantumDeterminants.GBasic.Hpk_herm k r), herm_perp k r z z' γ v hv c, star_zero]

lemma herm_add_smul {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (w v : Fin n → ℂ) (t : ℂ)
    (h1 : herm H v w = 0) (h2 : herm H w v = 0) :
    herm H (w + t • v) (w + t • v) = herm H w w + (star t * t) * herm H v v := by
  simp only [herm] at h1 h2 ⊢
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, star_add, star_smul, add_dotProduct,
    dotProduct_add, smul_dotProduct, dotProduct_smul, h1, h2, smul_eq_mul]
  ring

lemma blk_re {m : ℕ} (a : Fin m → ℂ) :
    (star (Sum.elim (0 : Fin m → ℂ) a) ⬝ᵥ
      (fromBlocks (1 : Matrix (Fin m) (Fin m) ℂ) 0 0 (-1) *ᵥ Sum.elim (0 : Fin m → ℂ) a)).re =
      -∑ b, Complex.normSq (a b) := by
  have hm : fromBlocks (1 : Matrix (Fin m) (Fin m) ℂ) 0 0 (-1) *ᵥ Sum.elim (0 : Fin m → ℂ) a =
      Sum.elim (0 : Fin m → ℂ) (-a) := by
    ext i
    cases i <;> simp [Matrix.fromBlocks_mulVec, Matrix.neg_mulVec, Matrix.one_mulVec]
  rw [hm]
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.star_apply,
    Pi.zero_apply, Pi.neg_apply, star_zero, zero_mul, Finset.sum_const_zero, zero_add,
    Complex.re_sum, Complex.normSq_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.star_def, Complex.conj_re,
    Complex.conj_im]
  ring

def emb (m : ℕ) : (Fin m → ℂ) →ₗ[ℂ] (Fin m ⊕ Fin m → ℂ) where
  toFun a := Sum.elim 0 a
  map_add' a b := by funext i; cases i <;> simp
  map_smul' c a := by funext i; cases i <;> simp

theorem uPos_of (hN : NegBound) : UPos := by
  intro k r z z' γ hs hp hdet hQ v hv hv0
  obtain ⟨Q, -, hQG⟩ := hQ
  by_contra hneg
  have hvv : (herm (Hpk k r) v v).re ≤ 0 := not_lt.mp hneg
  let L : (Fin (r + 1) → ℂ) →ₗ[ℂ] (Fin (2 * r + k + 1) → ℂ) :=
    (Matrix.mulVecLin (cols k r z z' γ * Q)).comp (emb (r + 1))
  have hLa : ∀ a, L a = cols k r z z' γ *ᵥ (Q *ᵥ Sum.elim 0 a) := by
    intro a
    show (cols k r z z' γ * Q) *ᵥ Sum.elim 0 a = _
    rw [Matrix.mulVec_mulVec]
  have hLre : ∀ a, (herm (Hpk k r) (L a) (L a)).re = -∑ b, Complex.normSq (a b) := by
    intro a
    rw [hLa, herm_cols, ← blk_re a, ← hQG, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  have hperp : ∀ a, herm (Hpk k r) v (L a) = 0 ∧ herm (Hpk k r) (L a) v = 0 := fun a => by
    rw [hLa]
    exact ⟨herm_perp k r z z' γ v hv _, herm_perp' k r z z' γ v hv _⟩
  let M : ((Fin (r + 1) → ℂ) × ℂ) →ₗ[ℂ] (Fin (2 * r + k + 1) → ℂ) :=
    L.coprod (LinearMap.toSpanSingleton ℂ _ v)
  have hM : ∀ p, M p = L p.1 + p.2 • v := fun p => by
    simp [M, LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply]
  have hMre : ∀ p, (herm (Hpk k r) (M p) (M p)).re =
      -∑ b, Complex.normSq (p.1 b) + Complex.normSq p.2 * (herm (Hpk k r) v v).re := by
    intro p
    have ht : star p.2 * p.2 = (Complex.normSq p.2 : ℂ) := by
      rw [Complex.normSq_eq_conj_mul_self]; rfl
    rw [hM, herm_add_smul _ _ _ _ (hperp p.1).1 (hperp p.1).2, Complex.add_re, hLre, ht,
      Complex.re_ofReal_mul]
  have hsum : ∀ a : Fin (r + 1) → ℂ, 0 ≤ ∑ b, Complex.normSq (a b) :=
    fun a => Finset.sum_nonneg fun b _ => Complex.normSq_nonneg _
  have hnp : ∀ x ∈ LinearMap.range M, (herm (Hpk k r) x x).re ≤ 0 := by
    rintro x ⟨p, rfl⟩
    rw [hMre]
    have h1 := hsum p.1
    have h2 : Complex.normSq p.2 * (herm (Hpk k r) v v).re ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) hvv
    linarith
  have hinj : Function.Injective M := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro p hp0
    have hre := hMre p
    rw [hp0] at hre
    have h0 : (herm (Hpk k r) (0 : Fin (2 * r + k + 1) → ℂ) 0).re = 0 := by simp [herm]
    rw [h0] at hre
    have h1 := hsum p.1
    have h2 : Complex.normSq p.2 * (herm (Hpk k r) v v).re ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (Complex.normSq_nonneg _) hvv
    have hs0 : ∑ b, Complex.normSq (p.1 b) = 0 := by linarith
    have ha : p.1 = 0 := by
      funext b
      have hb := (Finset.sum_eq_zero_iff_of_nonneg
        (fun b _ => Complex.normSq_nonneg (p.1 b))).1 hs0 b (Finset.mem_univ b)
      simpa using hb
    have ht : p.2 • v = 0 := by
      rw [hM, ha, map_zero, zero_add] at hp0
      exact hp0
    exact Prod.ext ha ((smul_eq_zero.1 ht).resolve_right hv0)
  have hdim := hN k r (LinearMap.range M) hnp
  rw [LinearMap.finrank_range_of_inj hinj] at hdim
  simp [Module.finrank_prod, Module.finrank_fin_fun] at hdim

end PI.FrameInd.UPosW
