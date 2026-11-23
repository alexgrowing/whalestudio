import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.ClsGainBSt

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Sw.WR.K.GB

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem pb_cd_entry (i j : Fin n) : ContDiff ℂ (⊤ : ℕ∞) (fun b : Mc n => b i j) :=
  contDiff_apply_apply (𝕜 := ℂ) (E := ℂ) i j

theorem pb_cd_det {f : Mc n → Mc n} (hf : ∀ i j, ContDiff ℂ (⊤ : ℕ∞) (fun b => f b i j)) :
    ContDiff ℂ (⊤ : ℕ∞) (fun b => (f b).det) := by
  have e : (fun b => (f b).det) =
      fun b => ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, f b (σ i) i := by
    funext b; rw [Matrix.det_apply']
  rw [e]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hf _ _)

theorem pb_cd_affine (a : ℂ) (e : ℂ) (i j : Fin n) :
    ContDiff ℂ (⊤ : ℕ∞) (fun b : Mc n => (1 + (e * a) • b) i j) := by
  have h : (fun b : Mc n => (1 + (e * a) • b) i j) = fun b => (1 : Mc n) i j + (e * a) * b i j := by
    funext b; simp [Matrix.add_apply, Matrix.smul_apply]
  rw [h]; exact contDiff_const.add (contDiff_const.mul (pb_cd_entry i j))

theorem pb_cd_adj {f : Mc n → Mc n} (hf : ∀ i j, ContDiff ℂ (⊤ : ℕ∞) (fun b => f b i j)) (i j : Fin n) :
    ContDiff ℂ (⊤ : ℕ∞) (fun b => (f b).adjugate i j) := by
  simp only [Matrix.adjugate_apply]
  apply pb_cd_det
  intro r c
  by_cases h : r = j
  · subst h; simp only [Matrix.updateRow_self]; exact contDiff_const
  · simp only [Matrix.updateRow_ne h]; exact hf r c

theorem pb_cdOn_inv {f : Mc n → Mc n} (hf : ∀ i j, ContDiff ℂ (⊤ : ℕ∞) (fun b => f b i j)) (s : Set (Mc n))
    (hs : ∀ b ∈ s, (f b).det ≠ 0) (i j : Fin n) : ContDiffOn ℂ (⊤ : ℕ∞) (fun b => (f b)⁻¹ i j) s := by
  have e : (fun b => (f b)⁻¹ i j) = fun b => ((f b).det)⁻¹ * (f b).adjugate i j := by
    funext b; rw [Matrix.inv_def, Ring.inverse_eq_inv]; simp [Matrix.smul_apply]
  rw [e]
  exact ((pb_cd_det hf).contDiffOn.inv hs).mul (pb_cd_adj hf i j).contDiffOn

theorem pb_cdOn_detInv {f : Mc n → Mc n} (hf : ∀ i j, ContDiff ℂ (⊤ : ℕ∞) (fun b => f b i j)) (s : Set (Mc n))
    (hs : ∀ b ∈ s, (f b).det ≠ 0) : ContDiffOn ℂ (⊤ : ℕ∞) (fun b => (f b)⁻¹.det) s := by
  have e : (fun b => (f b)⁻¹.det) = fun b => ((f b).det)⁻¹ := by
    funext b; rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  rw [e]; exact (pb_cd_det hf).contDiffOn.inv hs

theorem pb_cdOn_eval {ι : Type} (R : MvPolynomial ι ℂ) (v : ι → Mc n → ℂ) (s : Set (Mc n))
    (hv : ∀ k, ContDiffOn ℂ (⊤ : ℕ∞) (v k) s) :
    ContDiffOn ℂ (⊤ : ℕ∞) (fun b => MvPolynomial.eval (fun k => v k b) R) s := by
  induction R using MvPolynomial.induction_on with
  | C a => simpa using (contDiffOn_const : ContDiffOn ℂ (⊤ : ℕ∞) (fun _ : Mc n => a) s)
  | add p q hp hq => simpa using hp.add hq
  | mul_X p k hp => simpa using hp.mul (hv k)

theorem pb_eval_bound {ι : Type} (R : MvPolynomial ι ℂ) (B : ℝ) :
    ∃ C : ℝ, ∀ v : ι → ℂ, (∀ k, ‖v k‖ ≤ B) → ‖MvPolynomial.eval v R‖ ≤ C := by
  induction R using MvPolynomial.induction_on with
  | C a => exact ⟨‖a‖, fun v _ => by simp⟩
  | add p q hp hq =>
    obtain ⟨C1, h1⟩ := hp; obtain ⟨C2, h2⟩ := hq
    exact ⟨C1 + C2, fun v hv => by
      simp only [map_add]; exact (norm_add_le _ _).trans (add_le_add (h1 v hv) (h2 v hv))⟩
  | mul_X p k hp =>
    obtain ⟨C1, h1⟩ := hp
    exact ⟨max C1 0 * max B 0, fun v hv => by
      simp only [map_mul, MvPolynomial.eval_X, norm_mul]
      exact mul_le_mul ((h1 v hv).trans (le_max_left _ _)) ((hv k).trans (le_max_left _ _))
        (norm_nonneg _) (le_max_right _ _)⟩

theorem pb_norm_one_sub (a : ℂ) (ha : a = Complex.I ∨ a = -Complex.I) (l : ℝ) :
    (1 + |l|) / Real.sqrt 2 ≤ ‖1 - a * (l : ℂ)‖ := by
  have hsq : ‖1 - a * (l : ℂ)‖ ^ 2 = 1 + l ^ 2 := by
    rw [Complex.sq_norm]
    rcases ha with rfl | rfl <;> simp [Complex.normSq_apply] <;> ring
  have h2 : ((1 + |l|) / Real.sqrt 2) ^ 2 ≤ ‖1 - a * (l : ℂ)‖ ^ 2 := by
    rw [hsq, div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
    nlinarith [sq_abs l, sq_nonneg (1 - |l|), abs_nonneg l]
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 h2

def pbwt (lam : Fin n → ℝ) (i : Fin n) : ℝ := Real.sqrt (1 + |lam i|)

theorem pbwt_pos (lam : Fin n → ℝ) (i : Fin n) : 0 < pbwt lam i := Real.sqrt_pos.2 (by positivity)

theorem pb_one_le_wt (lam : Fin n → ℝ) (i : Fin n) : 1 ≤ pbwt lam i := by
  unfold pbwt; rw [Real.one_le_sqrt]; linarith [abs_nonneg (lam i)]

theorem pbwt_sq (lam : Fin n → ℝ) (i : Fin n) : pbwt lam i ^ 2 = 1 + |lam i| :=
  Real.sq_sqrt (by positivity)

theorem pb_dom (a : ℂ) (ha : a = Complex.I ∨ a = -Complex.I) (lam : Fin n → ℝ) (c₀ : ℝ) (hc : 0 ≤ c₀)
    (hc₀ : (n : ℝ) * c₀ ≤ 1 / 4) (b : Mc n)
    (hb : ∀ i j, ‖b i j - Matrix.diagonal (fun i => (lam i : ℂ)) i j‖ ≤ c₀ * (pbwt lam i * pbwt lam j))
    (x : Fin n → ℂ) (B : ℝ) (hy : ∀ i, ‖((1 - a • b) *ᵥ x) i‖ ≤ B * pbwt lam i) :
    ∀ i, pbwt lam i * ‖x i‖ ≤ 3 * B := by
  intro i
  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ (fun j => pbwt lam j * ‖x j‖) ⟨i, Finset.mem_univ _⟩
  set m := pbwt lam i0 * ‖x i0‖ with hmdef
  have hm : ∀ j, pbwt lam j * ‖x j‖ ≤ m := fun j => hi0 j (Finset.mem_univ _)
  have hm0 : 0 ≤ m := mul_nonneg (pbwt_pos lam i0).le (norm_nonneg _)
  have ha1 : ‖a‖ = 1 := by rcases ha with rfl | rfl <;> simp
  have hD : ∑ j, Matrix.diagonal (fun i => (lam i : ℂ)) i0 j * x j = (lam i0 : ℂ) * x i0 := by
    rw [Finset.sum_eq_single i0]
    · simp [Matrix.diagonal_apply_eq]
    · intro j _ hj; simp [Matrix.diagonal_apply_ne _ (Ne.symm hj)]
    · simp
  have row : ((1 - a • b) *ᵥ x) i0 = (1 - a * (lam i0 : ℂ)) * x i0 -
      a * ∑ j, (b i0 j - Matrix.diagonal (fun i => (lam i : ℂ)) i0 j) * x j := by
    have e1 : ((1 - a • b) *ᵥ x) i0 = x i0 - a * ∑ j, b i0 j * x j := by
      simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, sub_mul,
        Finset.sum_sub_distrib, Finset.mul_sum, Matrix.one_apply, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_assoc]
    rw [e1]; simp only [sub_mul, Finset.sum_sub_distrib, hD]; ring
  have hsum : ‖∑ j, (b i0 j - Matrix.diagonal (fun i => (lam i : ℂ)) i0 j) * x j‖ ≤ (n : ℝ) * (c₀ * pbwt lam i0 * m) := by
    calc ‖∑ j, (b i0 j - Matrix.diagonal (fun i => (lam i : ℂ)) i0 j) * x j‖ ≤ ∑ j, ‖(b i0 j - Matrix.diagonal (fun i => (lam i : ℂ)) i0 j) * x j‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin n, c₀ * pbwt lam i0 * m := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul]
        calc ‖(b i0 j - Matrix.diagonal (fun i => (lam i : ℂ)) i0 j)‖ * ‖x j‖ ≤ (c₀ * (pbwt lam i0 * pbwt lam j)) * ‖x j‖ :=
              mul_le_mul_of_nonneg_right (hb i0 j) (norm_nonneg _)
          _ = c₀ * pbwt lam i0 * (pbwt lam j * ‖x j‖) := by ring
          _ ≤ c₀ * pbwt lam i0 * m :=
              mul_le_mul_of_nonneg_left (hm j) (mul_nonneg hc (pbwt_pos lam i0).le)
      _ = (n : ℝ) * (c₀ * pbwt lam i0 * m) := by simp
  have hlow : (pbwt lam i0 / Real.sqrt 2) * m ≤ ‖(1 - a * (lam i0 : ℂ)) * x i0‖ := by
    rw [norm_mul]
    have h1 := pb_norm_one_sub a ha (lam i0)
    have : (pbwt lam i0 / Real.sqrt 2) * m = ((1 + |lam i0|) / Real.sqrt 2) * ‖x i0‖ := by
      rw [hmdef, ← pbwt_sq]; ring
    rw [this]; exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  have hup : ‖(1 - a * (lam i0 : ℂ)) * x i0‖ ≤ B * pbwt lam i0 + (n : ℝ) * (c₀ * pbwt lam i0 * m) := by
    have e : (1 - a * (lam i0 : ℂ)) * x i0 = ((1 - a • b) *ᵥ x) i0 + a * ∑ j, (b i0 j - Matrix.diagonal (fun i => (lam i : ℂ)) i0 j) * x j := by
      rw [row]; ring
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add (hy i0) ?_)
    rw [norm_mul, ha1, one_mul]; exact hsum
  have key : pbwt lam i0 * (m / Real.sqrt 2) ≤ pbwt lam i0 * (B + (n : ℝ) * c₀ * m) := by
    have := hlow.trans hup
    calc pbwt lam i0 * (m / Real.sqrt 2) = (pbwt lam i0 / Real.sqrt 2) * m := by ring
      _ ≤ B * pbwt lam i0 + (n : ℝ) * (c₀ * pbwt lam i0 * m) := this
      _ = pbwt lam i0 * (B + (n : ℝ) * c₀ * m) := by ring
  have key2 := le_of_mul_le_mul_left key (pbwt_pos lam i0)
  have hs2 : Real.sqrt 2 ≤ 10 / 7 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hsp : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hmd : m * (7 / 10) ≤ m / Real.sqrt 2 := by
    rw [le_div_iff₀ hsp]; nlinarith
  have hnc : (n : ℝ) * c₀ * m ≤ m / 4 := by nlinarith
  have hfin : m ≤ 3 * B := by nlinarith
  exact (hm i).trans hfin

theorem pb_inv (a : ℂ) (ha : a = Complex.I ∨ a = -Complex.I) (lam : Fin n → ℝ) (c₀ : ℝ) (hc : 0 ≤ c₀)
    (hc₀ : (n : ℝ) * c₀ ≤ 1 / 4) (b : Mc n)
    (hb : ∀ i j, ‖b i j - Matrix.diagonal (fun i => (lam i : ℂ)) i j‖ ≤ c₀ * (pbwt lam i * pbwt lam j)) :
    IsUnit (1 - a • b).det ∧ (∀ i j, ‖(1 - a • b)⁻¹ i j‖ ≤ 3 / (pbwt lam i * pbwt lam j)) := by
  have hdet : IsUnit (1 - a • b).det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    apply hv0
    funext i
    have := pb_dom a ha lam c₀ hc hc₀ b hb v 0 (fun i => by simp [hv]) i
    have hw := pbwt_pos lam i
    have : ‖v i‖ ≤ 0 := by nlinarith [norm_nonneg (v i)]
    simpa using le_antisymm this (norm_nonneg _)
  refine ⟨hdet, fun i j => ?_⟩
  set Y := 1 - a • b
  have hx : Y *ᵥ (Y⁻¹ *ᵥ Pi.single j 1) = Pi.single j 1 := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hwj := pbwt_pos lam j
  have key := pb_dom a ha lam c₀ hc hc₀ b hb (Y⁻¹ *ᵥ Pi.single j 1) (1 / pbwt lam j) (fun k => by
    rw [hx]
    by_cases hk : k = j
    · subst hk; simp [inv_mul_cancel₀ hwj.ne']
    · simp [Pi.single_apply, hk]; exact mul_nonneg (by positivity) (pbwt_pos lam k).le) i
  have e : (Y⁻¹ *ᵥ Pi.single j 1) i = Y⁻¹ i j := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [e] at key
  have hwi := pbwt_pos lam i
  rw [le_div_iff₀ (mul_pos hwi hwj)]
  calc ‖Y⁻¹ i j‖ * (pbwt lam i * pbwt lam j) = (pbwt lam i * ‖Y⁻¹ i j‖) * pbwt lam j := by ring
    _ ≤ (3 * (1 / pbwt lam j)) * pbwt lam j := mul_le_mul_of_nonneg_right key hwj.le
    _ = 3 := by field_simp

theorem pb_det_le (A : Mc n) (f : Fin n → ℝ) (K : ℝ)
    (hA : ∀ i j, ‖A i j‖ ≤ K / (f i * f j)) : ‖A.det‖ ≤ (Nat.factorial n : ℝ) * (K ^ n / (∏ i, f i) ^ 2) := by
  rw [Matrix.det_apply']
  have hterm : ∀ σ : Equiv.Perm (Fin n),
      ‖((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A (σ i) i‖ ≤ K ^ n / (∏ i, f i) ^ 2 := by
    intro σ
    have hs : ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
    rw [norm_mul, hs, one_mul, norm_prod]
    calc ∏ i, ‖A (σ i) i‖ ≤ ∏ i, K / (f (σ i) * f i) :=
          Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hA _ _)
      _ = K ^ n / (∏ i, f i) ^ 2 := by
          rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            Finset.prod_mul_distrib, Equiv.prod_comp σ f, sq]
  calc ‖∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A (σ i) i‖
      ≤ ∑ σ : Equiv.Perm (Fin n), ‖((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, A (σ i) i‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), K ^ n / (∏ i, f i) ^ 2 := Finset.sum_le_sum fun σ _ => hterm σ
    _ = (Nat.factorial n : ℝ) * (K ^ n / (∏ i, f i) ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

theorem pb_kk (k : Mc n) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) : k * kᴴ = 1 ∧ kᴴ * k = 1 :=
  ⟨by simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.1 hk,
   by simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.1 hk⟩

theorem pb_norm_det_unitary (k : Mc n) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) : ‖k.det‖ = 1 := by
  have h2 : k.det * star k.det = 1 := by
    rw [← Matrix.det_conjTranspose, ← Matrix.det_mul, (pb_kk k hk).1, Matrix.det_one]
  have h3 : Complex.normSq k.det = 1 := by
    have := h2; rw [Complex.star_def, Complex.mul_conj] at this; exact_mod_cast this
  have h4 : ‖k.det‖ ^ 2 = 1 := by rw [Complex.sq_norm, h3]
  nlinarith [norm_nonneg k.det, sq_nonneg (‖k.det‖ - 1)]

theorem pb_conj (c : ℂ) (k b : Mc n) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    1 - c • (k * b * kᴴ) = k * (1 - c • b) * kᴴ := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, (pb_kk k hk).1, Matrix.mul_smul, Matrix.smul_mul]

theorem pb_conj_inv (Y k : Mc n) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : IsUnit Y.det) :
    (k * Y * kᴴ)⁻¹ = k * Y⁻¹ * kᴴ := by
  apply Matrix.inv_eq_right_inv
  calc k * Y * kᴴ * (k * Y⁻¹ * kᴴ) = k * (Y * (kᴴ * k) * Y⁻¹) * kᴴ := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [(pb_kk k hk).2, Matrix.mul_one, Matrix.mul_nonsing_inv _ hY, Matrix.mul_one, (pb_kk k hk).1]

theorem pb_conj_unit (Y k : Mc n) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (hY : IsUnit Y.det) :
    IsUnit (k * Y * kᴴ).det := by
  rw [isUnit_iff_ne_zero, Matrix.det_mul, Matrix.det_mul]
  have h1 : k.det ≠ 0 := fun h => by simpa [h] using pb_norm_det_unitary k hk
  have h2 : kᴴ.det ≠ 0 := by
    rw [Matrix.det_conjTranspose]; exact fun h => h1 (by simpa using h)
  exact mul_ne_zero (mul_ne_zero h1 (isUnit_iff_ne_zero.1 hY)) h2

theorem pb_conj_entry (M k : Mc n) (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (K : ℝ)
    (hM : ∀ a b, ‖M a b‖ ≤ K) (i j : Fin n) : ‖(k * M * kᴴ) i j‖ ≤ (n : ℝ) * ((n : ℝ) * K) := by
  have hk' : kᴴ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
    simpa [Matrix.star_eq_conjTranspose] using Unitary.star_mem hk
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ b, ‖(k * M) i b * kᴴ b j‖ ≤ ∑ _b : Fin n, (n : ℝ) * K := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [norm_mul, Matrix.mul_apply]
        have e2 : ‖kᴴ b j‖ ≤ 1 := entry_norm_bound_of_unitary hk' b j
        have e1 : ‖∑ a, k i a * M a b‖ ≤ (n : ℝ) * K := by
          refine (norm_sum_le _ _).trans ?_
          calc ∑ a, ‖k i a * M a b‖ ≤ ∑ _a : Fin n, K := by
                refine Finset.sum_le_sum fun a _ => ?_
                rw [norm_mul]
                calc ‖k i a‖ * ‖M a b‖ ≤ 1 * K :=
                      mul_le_mul (entry_norm_bound_of_unitary hk i a) (hM a b) (norm_nonneg _) zero_le_one
                  _ = K := one_mul K
            _ = (n : ℝ) * K := by simp
        calc ‖∑ a, k i a * M a b‖ * ‖kᴴ b j‖ ≤ ((n : ℝ) * K) * 1 :=
              mul_le_mul e1 e2 (norm_nonneg _) ((norm_nonneg _).trans e1)
          _ = (n : ℝ) * K := mul_one _
    _ = (n : ℝ) * ((n : ℝ) * K) := by simp

theorem pb_cd_oneSub (c : ℂ) (i j : Fin n) : ContDiff ℂ (⊤ : ℕ∞) (fun b : Mc n => (1 - c • b) i j) := by
  have h : (fun b : Mc n => (1 - c • b) i j) = fun b => (1 + ((-1) * c) • b) i j := by
    funext b; simp [sub_eq_add_neg, neg_smul]
  rw [h]; exact pb_cd_affine c (-1) i j

theorem pBound : PBound := by
  intro n s hs p q R
  have ha : Complex.I * s = Complex.I ∨ Complex.I * s = -Complex.I := by rcases hs with rfl | rfl <;> simp
  have ham : -(Complex.I * s) = Complex.I ∨ -(Complex.I * s) = -Complex.I := by
    rcases ha with h | h <;> simp [h]
  have hplus : ∀ b : Mc n, (1 + (Complex.I * s) • b) = 1 - (-(Complex.I * s)) • b := by
    intro b; rw [neg_smul, sub_neg_eq_add]
  have he1 : ∀ i j, ContDiff ℂ (⊤ : ℕ∞) (fun b : Mc n => (1 - (Complex.I * s) • b) i j) :=
    fun i j => pb_cd_oneSub _ i j
  have he2 : ∀ i j, ContDiff ℂ (⊤ : ℕ∞) (fun b : Mc n => (1 + (Complex.I * s) • b) i j) := fun i j => by
    simpa [one_mul] using pb_cd_affine (Complex.I * s) 1 i j
  have hd1 := pb_cd_det he1
  have hd2 := pb_cd_det he2
  have hopen : IsOpen (Ugood (n := n) s) := by
    have e : Ugood (n := n) s = {b | (1 - (Complex.I * s) • b).det ≠ 0} ∩ {b | (1 + (Complex.I * s) • b).det ≠ 0} := by
      ext b; simp [Ugood, isUnit_iff_ne_zero]
    rw [e]
    exact (isOpen_ne_fun hd1.continuous continuous_const).inter (isOpen_ne_fun hd2.continuous continuous_const)
  have hne1 : ∀ b ∈ Ugood (n := n) s, (1 - (Complex.I * s) • b).det ≠ 0 := fun b hb => isUnit_iff_ne_zero.1 hb.1
  have hne2 : ∀ b ∈ Ugood (n := n) s, (1 + (Complex.I * s) • b).det ≠ 0 := fun b hb => isUnit_iff_ne_zero.1 hb.2
  have hsmooth : ContDiffOn ℂ (⊤ : ℕ∞) (Fr s p q R) (Ugood s) := by
    have hv : ∀ k : Bool × Fin n × Fin n, ContDiffOn ℂ (⊤ : ℕ∞) (fun b : Mc n => if k.1 then
        (1 + (Complex.I * s) • b)⁻¹ k.2.1 k.2.2 else (1 - (Complex.I * s) • b)⁻¹ k.2.1 k.2.2) (Ugood s) := by
      rintro ⟨t, i, j⟩
      cases t
      · simpa using pb_cdOn_inv he1 _ hne1 i j
      · simpa using pb_cdOn_inv he2 _ hne2 i j
    exact (((pb_cdOn_detInv he1 _ hne1).pow p).mul ((pb_cdOn_detInv he2 _ hne2).pow q)).mul
      (pb_cdOn_eval R _ _ hv)
  obtain ⟨CR, hCR⟩ := pb_eval_bound R ((n : ℝ) * ((n : ℝ) * 3))
  refine ⟨hopen, hsmooth, 1 / (4 * (n : ℝ) + 4),
    ((Nat.factorial n : ℝ) * 3 ^ n) ^ p * ((Nat.factorial n : ℝ) * 3 ^ n) ^ q * CR, by positivity, ?_⟩
  intro k hk lam b hb
  set K1 : ℝ := (Nat.factorial n : ℝ) * 3 ^ n with hK1def
  have hc₀ : (n : ℝ) * (1 / (4 * (n : ℝ) + 4)) ≤ 1 / 4 := by
    rw [mul_one_div, div_le_iff₀ (by positivity)]; linarith
  have hb' : ∀ i j, ‖b i j - Matrix.diagonal (fun i => (lam i : ℂ)) i j‖ ≤
      (1 / (4 * (n : ℝ) + 4)) * (pbwt lam i * pbwt lam j) := by
    intro i j
    have := hb i j
    simpa [pbwt, Real.sqrt_mul (by positivity : (0:ℝ) ≤ 1 + |lam i|)] using this
  obtain ⟨hu1, hY1⟩ := pb_inv _ ha lam _ (by positivity) hc₀ b hb'
  obtain ⟨hu2, hY2⟩ := pb_inv _ ham lam _ (by positivity) hc₀ b hb'
  have c1 : 1 - (Complex.I * s) • (k * b * kᴴ) = k * (1 - (Complex.I * s) • b) * kᴴ := pb_conj _ k b hk
  have c2 : 1 + (Complex.I * s) • (k * b * kᴴ) = k * (1 - (-(Complex.I * s)) • b) * kᴴ := by
    rw [hplus]; exact pb_conj _ k b hk
  refine ⟨⟨by rw [c1]; exact pb_conj_unit _ k hk hu1, by rw [c2]; exact pb_conj_unit _ k hk hu2⟩, ?_⟩
  have i1 : (1 - (Complex.I * s) • (k * b * kᴴ))⁻¹ = k * (1 - (Complex.I * s) • b)⁻¹ * kᴴ := by
    rw [c1]; exact pb_conj_inv _ k hk hu1
  have i2 : (1 + (Complex.I * s) • (k * b * kᴴ))⁻¹ = k * (1 - (-(Complex.I * s)) • b)⁻¹ * kᴴ := by
    rw [c2]; exact pb_conj_inv _ k hk hu2
  set P : ℝ := ∏ i, (1 + |lam i|) with hPdef
  have hP : 0 < P := Finset.prod_pos fun i _ => by positivity
  have hPw : (∏ i, pbwt lam i) ^ 2 = P := by
    rw [← Finset.prod_pow]; exact Finset.prod_congr rfl fun i _ => pbwt_sq lam i
  have hdetY : ∀ (Y : Mc n), (∀ i j, ‖Y i j‖ ≤ 3 / (pbwt lam i * pbwt lam j)) → ‖Y.det‖ ≤ K1 / P := by
    intro Y hYb
    have := pb_det_le Y (pbwt lam) 3 hYb
    rw [hPw] at this
    calc ‖Y.det‖ ≤ (Nat.factorial n : ℝ) * (3 ^ n / P) := this
      _ = K1 / P := by rw [hK1def]; ring
  have hdc : ∀ (Y : Mc n), ‖(k * Y * kᴴ).det‖ = ‖Y.det‖ := by
    intro Y
    rw [Matrix.det_mul, Matrix.det_mul, norm_mul, norm_mul, pb_norm_det_unitary k hk, Matrix.det_conjTranspose,
      norm_star, pb_norm_det_unitary k hk, one_mul, mul_one]
  have hdet1 : ‖(1 - (Complex.I * s) • (k * b * kᴴ))⁻¹.det‖ ≤ K1 / P := by
    rw [i1, hdc]; exact hdetY _ hY1
  have hdet2 : ‖(1 + (Complex.I * s) • (k * b * kᴴ))⁻¹.det‖ ≤ K1 / P := by
    rw [i2, hdc]; exact hdetY _ hY2
  have hent : ∀ (Y : Mc n), (∀ i j, ‖Y i j‖ ≤ 3 / (pbwt lam i * pbwt lam j)) →
      ∀ i j, ‖(k * Y * kᴴ) i j‖ ≤ (n : ℝ) * ((n : ℝ) * 3) := by
    intro Y hYb i j
    refine pb_conj_entry Y k hk 3 (fun a c => (hYb a c).trans ?_) i j
    rw [div_le_iff₀ (mul_pos (pbwt_pos lam a) (pbwt_pos lam c))]
    nlinarith [pb_one_le_wt lam a, pb_one_le_wt lam c]
  have hev : ‖MvPolynomial.eval (fun k' : Bool × Fin n × Fin n => if k'.1 then
      (1 + (Complex.I * s) • (k * b * kᴴ))⁻¹ k'.2.1 k'.2.2 else (1 - (Complex.I * s) • (k * b * kᴴ))⁻¹ k'.2.1 k'.2.2) R‖
      ≤ CR := by
    apply hCR
    rintro ⟨t, i, j⟩
    cases t
    · simp only [Bool.false_eq_true, if_false]; rw [i1]; exact hent _ hY1 i j
    · simp only [if_true]; rw [i2]; exact hent _ hY2 i j
  have hrp : P ^ (-((p + q : ℕ) : ℝ)) = (P ^ (p + q))⁻¹ := by
    rw [Real.rpow_neg hP.le, Real.rpow_natCast]
  show ‖(1 - (Complex.I * s) • (k * b * kᴴ))⁻¹.det ^ p * (1 + (Complex.I * s) • (k * b * kᴴ))⁻¹.det ^ q *
      MvPolynomial.eval (fun k' : Bool × Fin n × Fin n => if k'.1 then
      (1 + (Complex.I * s) • (k * b * kᴴ))⁻¹ k'.2.1 k'.2.2 else (1 - (Complex.I * s) • (k * b * kᴴ))⁻¹ k'.2.1 k'.2.2) R‖
      ≤ K1 ^ p * K1 ^ q * CR * P ^ (-((p + q : ℕ) : ℝ))
  rw [hrp, norm_mul, norm_mul, norm_pow, norm_pow]
  have hK1 : 0 ≤ K1 := by positivity
  calc _ ≤ (K1 / P) ^ p * (K1 / P) ^ q * CR := by gcongr
    _ = K1 ^ p * K1 ^ q * CR * (P ^ (p + q))⁻¹ := by
      rw [div_pow, div_pow, pow_add, mul_inv, div_eq_mul_inv, div_eq_mul_inv]; ring

end PositivityTheory.Rg.Sw.WR.K.GB
