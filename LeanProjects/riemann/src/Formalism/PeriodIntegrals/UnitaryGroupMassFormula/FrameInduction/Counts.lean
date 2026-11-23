import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameInduction.NonposCount

open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C2

noncomputable section
namespace PI.FrameInd.CountsW

open PI.FrameInd

def extZ {n : Type*} (p : n → Prop) [DecidablePred p] : ({i // p i} → ℂ) →ₗ[ℂ] (n → ℂ) where
  toFun y i := if h : p i then y ⟨i, h⟩ else 0
  map_add' y y' := by funext i; by_cases h : p i <;> simp [h]
  map_smul' c y := by funext i; by_cases h : p i <;> simp [h]

lemma extZ_apply {n : Type*} (p : n → Prop) [DecidablePred p] (y : {i // p i} → ℂ) (i : n) :
    extZ p y i = if h : p i then y ⟨i, h⟩ else 0 := rfl

lemma extZ_eq_zero {n : Type*} (p : n → Prop) [DecidablePred p] (y : {i // p i} → ℂ)
    (hy : extZ p y = 0) : y = 0 := by
  funext ⟨i, h⟩
  have h1 := congrFun hy i
  simpa [extZ_apply, h] using h1

lemma diag_eq {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * A * (hA.eigenvectorUnitary : Matrix n n ℂ) =
      diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) := by
  have h := hA.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_apply] at h
  simpa [Matrix.star_eq_conjTranspose, Function.comp_def] using h

lemma U_eq_zero {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (w : n → ℂ) (hw : (hA.eigenvectorUnitary : Matrix n n ℂ) *ᵥ w = 0) : w = 0 := by
  have hu : star (hA.eigenvectorUnitary : Matrix n n ℂ) * (hA.eigenvectorUnitary : Matrix n n ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.1 hA.eigenvectorUnitary.2
  calc w = (star (hA.eigenvectorUnitary : Matrix n n ℂ) * (hA.eigenvectorUnitary : Matrix n n ℂ)) *ᵥ w := by
        rw [hu, Matrix.one_mulVec]
    _ = star (hA.eigenvectorUnitary : Matrix n n ℂ) *ᵥ ((hA.eigenvectorUnitary : Matrix n n ℂ) *ᵥ w) := by
        rw [Matrix.mulVec_mulVec]
    _ = 0 := by rw [hw, Matrix.mulVec_zero]

lemma re_diag {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (w : n → ℂ) :
    (herm A ((hA.eigenvectorUnitary : Matrix n n ℂ) *ᵥ w) ((hA.eigenvectorUnitary : Matrix n n ℂ) *ᵥ w)).re =
      ∑ i, hA.eigenvalues i * Complex.normSq (w i) := by
  rw [herm_mulVec_mulVec, diag_eq, herm, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp [mulVec_diagonal, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

lemma blockA_re (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (γ : B.Mat k r) (hz : inWb k r z)
    (c : Fin (r + 1) ⊕ Fin (r + 1) → ℂ) (hc : ∀ b, c (Sum.inr b) = 0) :
    (herm (gramM k r z z' γ) c c).re =
      (herm (Hpk k r) z z).re * Complex.normSq (c (Sum.inl (Fin.last r))) := by
  have hb : ∀ a b, gramM k r z z' γ (Sum.inl a) (Sum.inl b) = (herm (Hpk k r) z z • ggLastU r) a b :=
    fun a b => ggBlockA k r z hz a b
  simp only [herm, dotProduct, mulVec, Fintype.sum_sum_type, hc, star_zero, zero_mul, mul_zero,
    Finset.sum_const_zero, add_zero, hb, Matrix.smul_apply, smul_eq_mul, Pi.star_apply]
  rw [Finset.sum_eq_single (Fin.last r) (fun a _ ha => by simp [ggLastU, ha]) (by simp)]
  rw [Finset.sum_eq_single (Fin.last r) (fun b _ hb => by simp [ggLastU, hb]) (by simp)]
  simp [ggLastU, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem positive_count : PosCount := by
  intro k r z z' γ hs hp hdet
  set hA := isHerm k r z z' γ with hhA
  let p : Fin (r + 1) ⊕ Fin (r + 1) → Prop := fun i => 0 < hA.eigenvalues i
  let ψ : ({i // p i} → ℂ) →ₗ[ℂ] (Fin (r + 1) → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (Sum.inr : Fin (r + 1) → Fin (r + 1) ⊕ Fin (r + 1))).comp
      ((Matrix.mulVecLin (hA.eigenvectorUnitary : Matrix _ _ ℂ)).comp (extZ p))
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have hinr : ∀ b, ((hA.eigenvectorUnitary : Matrix (Fin (r + 1) ⊕ Fin (r + 1))
        (Fin (r + 1) ⊕ Fin (r + 1)) ℂ) *ᵥ extZ p y) (Sum.inr b) = 0 := by
      intro b
      have := congrFun hy b
      simpa [ψ, LinearMap.funLeft_apply] using this
    have h1 := re_diag hA (extZ p y)
    rw [blockA_re k r z z' γ hs.2.1.1 _ hinr] at h1
    have hT : (herm (Hpk k r) z z).re < 0 := by
      have := hs.2.1.2; simp only [Tz] at this; linarith
    have hl : (herm (Hpk k r) z z).re *
        Complex.normSq (((hA.eigenvectorUnitary : Matrix (Fin (r + 1) ⊕ Fin (r + 1))
          (Fin (r + 1) ⊕ Fin (r + 1)) ℂ) *ᵥ extZ p y) (Sum.inl (Fin.last r))) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hT.le (Complex.normSq_nonneg _)
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin (r + 1) ⊕ Fin (r + 1))),
        0 ≤ hA.eigenvalues i * Complex.normSq (extZ p y i) := by
      intro i _
      rw [extZ_apply]
      split_ifs with h
      · exact mul_nonneg h.le (Complex.normSq_nonneg _)
      · simp
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1
      (le_antisymm (h1 ▸ hl) (Finset.sum_nonneg hnn))
    funext t
    have := hz t.1 (Finset.mem_univ _)
    rw [extZ_apply, dif_pos t.2] at this
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (ne_of_gt t.2)
    · simpa [Complex.normSq_eq_zero] using h
  have := LinearMap.finrank_le_finrank_of_injective hinj
  simpa [Module.finrank_fintype_fun_eq_card] using this

theorem nonposCount_of (hN : NegBound) : NonposCount := by
  intro k r z z' γ hs hp hdet
  set hA := isHerm k r z z' γ with hhA
  let q : Fin (r + 1) ⊕ Fin (r + 1) → Prop := fun i => ¬ 0 < hA.eigenvalues i
  let Φ : ({i // q i} → ℂ) →ₗ[ℂ] (Fin (2 * r + k + 1) → ℂ) :=
    (Matrix.mulVecLin (Vc k r z z' γ)).comp
      ((Matrix.mulVecLin (hA.eigenvectorUnitary : Matrix _ _ ℂ)).comp (extZ q))
  have hΦ : ∀ y, Φ y = Vc k r z z' γ *ᵥ ((hA.eigenvectorUnitary : Matrix _ _ ℂ) *ᵥ extZ q y) :=
    fun y => rfl
  have hre : ∀ y, (herm (Hpk k r) (Φ y) (Φ y)).re ≤ 0 := by
    intro y
    rw [hΦ, herm_Vc, re_diag]
    apply Finset.sum_nonpos
    intro i _
    rw [extZ_apply]
    split_ifs with h
    · exact mul_nonpos_of_nonpos_of_nonneg (not_lt.1 h) (Complex.normSq_nonneg _)
    · simp
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    rw [hΦ] at hy
    exact extZ_eq_zero q y (U_eq_zero hA _ (Vc_inj k r z z' γ hdet _ hy))
  have h1 := hN k r (LinearMap.range Φ) (by rintro x ⟨y, rfl⟩; exact hre y)
  rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card] at h1
  exact h1

end PI.FrameInd.CountsW
