import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.RowsZStrictMono

noncomputable section

namespace PI.WGL.XiB

open Formalism.BasicNotions MvPolynomial

theorem teleA {G : Type*} [AddCommGroup G] (n : ℕ) (P : ℕ → G) (hP0 : P 0 = 0) (w : G) (ℓ σ : ℕ → ℤ) :
    ℓ n • (P n + w) + ∑ i ∈ Finset.range n, ((σ i - ℓ (i + 1)) • P (i + 1) + (ℓ i - σ i) • (P i + w)) =
    (∑ j ∈ Finset.range n, σ j • (P (j + 1) - P j)) +
      ((∑ p ∈ Finset.range (n + 1), ℓ p) - ∑ j ∈ Finset.range n, σ j) • w := by
  induction n with
  | zero => simp [hP0]
  | succ n ih =>
    rw [Finset.sum_range_succ, eq_sub_of_add_eq' ih]
    simp only [Finset.sum_range_succ]
    simp only [smul_add, smul_sub, add_smul, sub_smul]
    abel

theorem teleM {G : Type*} [CommGroup G] (n : ℕ) (P : ℕ → G) (hP0 : P 0 = 1) (w : G) (ℓ σ : ℕ → ℤ) :
    (P n * w) ^ ℓ n * ∏ i ∈ Finset.range n, (P (i + 1) ^ (σ i - ℓ (i + 1)) * (P i * w) ^ (ℓ i - σ i)) =
    (∏ j ∈ Finset.range n, (P (j + 1) / P j) ^ σ j) *
      w ^ ((∑ p ∈ Finset.range (n + 1), ℓ p) - ∑ j ∈ Finset.range n, σ j) := by
  have h := teleA (G := Additive G) n (fun i => Additive.ofMul (P i)) (by simp [hP0])
    (Additive.ofMul w) ℓ σ
  have h2 := congrArg Additive.toMul h
  simpa [toMul_sum, toMul_zsmul, toMul_sub, toMul_add, mul_zpow] using h2

theorem diag_scalar {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg)
    (s : Fin N → ℂˣ) :
    detPow ℂ N (diagGL ℂ N s) lam.detShift * XiA.xiScal h lam sg (Matrix.diagonal fun a => (s a : ℂ)) =
      (((∏ j : Fin n, s ⟨j.1, by omega⟩ ^ sg.w j) * s ⟨n, by omega⟩ ^ degZ lam sg : ℂˣ) : ℂ) := by
  subst h
  set v : ℕ → ℂˣ := fun p => if hp : p < n + 1 then s ⟨p, hp⟩ else 1 with hv
  set P : ℕ → ℂˣ := fun k => ∏ p ∈ Finset.range k, v p with hP
  set ℓ : ℕ → ℤ := fun k => if hk : k < n + 1 then lam.w ⟨k, hk⟩ else 0 with hℓ
  set σ : ℕ → ℤ := fun k => if hk : k < n then sg.w ⟨k, hk⟩ else 0 with hσ
  set w : ℂˣ := s ⟨n, by omega⟩ with hw
  have hPa : ∀ k (hk : k ≤ n + 1), ∏ p : Fin k, s (Fin.castLE hk p) = P k := by
    intro k hk
    show ∏ p : Fin k, s (Fin.castLE hk p) = ∏ p ∈ Finset.range k, v p
    rw [← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl (fun p _ => ?_)
    have : p.1 < n + 1 := by omega
    simp only [hv, dif_pos this]
    rfl
  have hPs : ∀ k, P (k + 1) = P k * v k := fun k => by simp only [hP, Finset.prod_range_succ]
  have hdet : Matrix.GeneralLinearGroup.det (diagGL ℂ (n + 1) s) = P n * w := by
    ext
    have e := hPa (n + 1) le_rfl
    simp only [Fin.castLE_rfl, id] at e
    rw [hPs, show v n = w by simp [hv, hw]] at e
    rw [← e]
    simp [diagGL, Matrix.det_diagonal]
  have hshift : lam.detShift = ℓ n := by
    simp [DomWeight.detShift, hℓ]
  have hx : XiA.xiScal rfl lam sg (Matrix.diagonal fun a => (s a : ℂ)) =
      ((∏ i ∈ Finset.range n, (P (i + 1) ^ (σ i - ℓ (i + 1)) * (P i * w) ^ (ℓ i - σ i)) : ℂˣ) : ℂ) := by
    rw [← Fin.prod_univ_eq_prod_range (fun i => P (i + 1) ^ (σ i - ℓ (i + 1)) * (P i * w) ^ (ℓ i - σ i)) n]
    unfold XiA.xiScal
    rw [Units.coe_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    have hi := i.2
    have hA : 0 ≤ aa rfl lam sg i := by have := (hI i).2; unfold aa; omega
    have hB : 0 ≤ bb rfl lam sg i := by have := (hI i).1; unfold bb; omega
    have e1 : ∏ p : Fin (i.1 + 1), (Matrix.diagonal fun a => (s a : ℂ)) (Fin.castLE (by omega) p)
        (Fin.castLE (by omega) p) = ((P (i.1 + 1) : ℂˣ) : ℂ) := by
      rw [← hPa (i.1 + 1) (by omega), Units.coe_prod]
      simp [Matrix.diagonal_apply_eq]
    have e2 : ∏ p : Fin (i.1 + 1), (Matrix.diagonal fun a => (s a : ℂ)) (rowsZ rfl i p) (rowsZ rfl i p) =
        ((P i.1 * w : ℂˣ) : ℂ) := by
      simp only [Matrix.diagonal_apply_eq]
      rw [Fin.prod_univ_castSucc, ← hPa i.1 (by omega), Units.val_mul, Units.coe_prod]
      congr 1
      · refine Finset.prod_congr rfl (fun p _ => ?_)
        have : (Fin.castSucc p).1 ≠ i.1 := by simp; omega
        simp only [rowsZ, this, if_false]
        rfl
      · simp only [rowsZ, Fin.val_last, if_true, hw]
        congr 2
    rw [e1, e2, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
    congr 1
    rw [← zpow_natCast, ← zpow_natCast, Int.toNat_of_nonneg hA, Int.toNat_of_nonneg hB]
    congr 2
    · simp [aa, hσ, hℓ, hi]
    · simp [bb, hσ, hℓ, hi]
  have htarget : ((∏ j : Fin n, s ⟨j.1, by omega⟩ ^ sg.w j) * s ⟨n, by omega⟩ ^ degZ lam sg : ℂˣ) =
      (∏ j ∈ Finset.range n, (P (j + 1) / P j) ^ σ j) *
        w ^ ((∑ p ∈ Finset.range (n + 1), ℓ p) - ∑ j ∈ Finset.range n, σ j) := by
    congr 1
    · rw [← Fin.prod_univ_eq_prod_range (fun j => (P (j + 1) / P j) ^ σ j) n]
      refine Finset.prod_congr rfl (fun j _ => ?_)
      have hj := j.2
      rw [hPs, mul_div_cancel_left]
      simp [hv, hσ, hj, show j.1 < n + 1 by omega]
    · congr 1
      unfold degZ wsum
      rw [← Fin.sum_univ_eq_sum_range ℓ (n + 1), ← Fin.sum_univ_eq_sum_range σ n]
      congr 1
      · refine Finset.sum_congr rfl (fun p _ => ?_)
        simp only [hℓ]; rw [dif_pos p.2]
      · refine Finset.sum_congr rfl (fun p _ => ?_)
        simp only [hσ]; rw [dif_pos p.2]
  unfold detPow
  rw [hx, hdet, hshift, htarget, ← Units.val_mul, teleM n P (by simp [hP]) w ℓ σ]

theorem sqAct_diag_xi {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg)
    (s : Fin N → ℂˣ) :
    sqAct ℂ N lam (diagGL ℂ N s) (xi ℂ h lam sg) =
      (((∏ j : Fin n, s ⟨j.1, by omega⟩ ^ sg.w j) * s ⟨n, by omega⟩ ^ degZ lam sg : ℂˣ) : ℂ) • xi ℂ h lam sg := by
  have hG : XiA.GoodG n h (Matrix.diagonal fun a => (s a : ℂ)) := by
    unfold XiA.GoodG
    refine ⟨fun a b hab => ?_, fun b hb => ?_⟩
    · exact Matrix.diagonal_apply_ne _ (ne_of_lt hab).symm
    · apply Matrix.diagonal_apply_ne
      intro e
      apply hb
      rw [e]
  have hcoe : ((diagGL ℂ N s : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) =
      Matrix.diagonal fun a => (s a : ℂ) := by
    ext i j
    unfold diagGL
    simp [Matrix.diagonal_apply]
  unfold sqAct
  rw [hcoe, XiA.rowAct_xi h lam sg _ hG, MvPolynomial.C_mul', smul_smul, diag_scalar h lam sg hI s]

theorem embGL_diag {n N : ℕ} (h : n + 1 = N) (t : Fin n → ℂˣ) :
    embGL ℂ n N h (diagGL ℂ n t) = diagGL ℂ N (fun a => if ha : a.1 < n then t ⟨a.1, ha⟩ else 1) := by
  apply Units.ext
  ext a b
  rw [XiA.embGL_apply]
  unfold diagGL
  simp only [Matrix.diagonal_apply]
  by_cases ha : a.1 < n
  · by_cases hb : b.1 < n
    · simp only [ha, hb, dite_true]
      by_cases hab : a = b
      · subst hab
        simp
      · have hab' : (⟨a.1, ha⟩ : Fin n) ≠ ⟨b.1, hb⟩ := fun e => hab (Fin.ext (Fin.mk.inj_iff.mp e))
        simp [hab, hab']
    · have hab : a ≠ b := fun e => hb (e ▸ ha)
      simp [ha, hb, hab]
  · by_cases hb : b.1 < n
    · have hab : a ≠ b := fun e => ha (e ▸ hb)
      simp [ha, hb, hab]
    · have hab : a = b := Fin.ext (by omega)
      subst hab
      simp [ha]

theorem xi_torus {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg)
    (t : Fin n → ℂˣ) :
    sqAct ℂ N lam (embGL ℂ n N h (diagGL ℂ n t)) (xi ℂ h lam sg) =
      ((∏ j, t j ^ sg.w j : ℂˣ) : ℂ) • xi ℂ h lam sg := by
  rw [embGL_diag, sqAct_diag_xi h lam sg hI]
  simp

theorem xi_last {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg)
    (a : ℂˣ) :
    sqAct ℂ N lam (lastGL ℂ N a) (xi ℂ h lam sg) = ((a ^ degZ lam sg : ℂˣ) : ℂ) • xi ℂ h lam sg := by
  have hL : lastGL ℂ N a = diagGL ℂ N (fun b => if b.1 < n then 1 else a) := by
    apply Units.ext
    ext i j
    unfold lastGL diagGL
    simp [Matrix.diagonal_apply]
    split_ifs <;> simp_all <;> omega
  rw [hL, sqAct_diag_xi h lam sg hI]
  simp

theorem xi_unitri {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
    (g : GL (Fin n) ℂ) (hlow : ∀ i j, j < i → (g : Matrix (Fin n) (Fin n) ℂ) i j = 0)
    (hdiag : ∀ i, (g : Matrix (Fin n) (Fin n) ℂ) i i = 1) :
    sqAct ℂ N lam (embGL ℂ n N h g) (xi ℂ h lam sg) = xi ℂ h lam sg := by
  set G := ((embGL ℂ n N h g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) with hGdef
  have hlowG : ∀ a b : Fin N, a < b → G b a = 0 := by
    intro a b hab
    have hab' := Fin.lt_def.mp hab
    rw [hGdef, XiA.embGL_apply]
    by_cases hb : b.1 < n
    · have ha : a.1 < n := by omega
      rw [dif_pos hb, dif_pos ha]
      exact hlow _ _ (Fin.mk_lt_mk.mpr hab')
    · have hbN := b.isLt
      rw [dif_neg hb, if_pos (by omega)]
  have hcol : ∀ b : Fin N, b.1 ≠ n → G b ⟨n, by omega⟩ = 0 := by
    intro b hb
    have hbN := b.isLt
    have hb' : b.1 < n := by omega
    rw [hGdef, XiA.embGL_apply, dif_pos hb', dif_neg (lt_irrefl n)]
  have hdg : ∀ a : Fin N, G a a = 1 := by
    intro a
    rw [hGdef, XiA.embGL_apply]
    by_cases ha : a.1 < n
    · rw [dif_pos ha, dif_pos ha]
      exact hdiag ⟨a.1, ha⟩
    · rw [dif_neg ha, if_neg ha]
  have hgood : XiA.GoodG n h G := by
    unfold XiA.GoodG
    exact ⟨hlowG, hcol⟩
  have hdet : G.det = 1 := by
    rw [Matrix.det_of_upperTriangular (fun i j hij => hlowG j i hij)]
    simp [hdg]
  have hxs : XiA.xiScal h lam sg G = 1 := by
    unfold XiA.xiScal
    simp [hdg]
  unfold sqAct
  rw [XiA.rowAct_xi h lam sg G hgood, hxs, MvPolynomial.C_1, one_mul]
  have hdu : Matrix.GeneralLinearGroup.det (embGL ℂ n N h g) = 1 := by
    apply Units.ext
    rw [Units.val_one, Matrix.GeneralLinearGroup.val_det_apply, ← hGdef, hdet]
  unfold detPow
  rw [hdu]
  simp

private theorem mul_mem_dualWeyl_complex_add {N : ℕ} (ν μ : Fin N → ℕ) (f g : MvPolynomial (Fin N × Fin N) ℂ)
    (hf : f ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N ν) (hg : g ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N μ) :
    f * g ∈ Formalism.GradedWeylDivisibility.dualWeyl ℂ N N (ν + μ) := by
  unfold Formalism.GradedWeylDivisibility.dualWeyl at hf hg ⊢
  rw [Submodule.mem_inf] at hf hg ⊢
  obtain ⟨hf1, hf2⟩ := hf
  obtain ⟨hg1, hg2⟩ := hg
  refine ⟨?_, ?_⟩
  · rw [MvPolynomial.mem_weightedHomogeneousSubmodule] at hf1 hg1 ⊢
    exact hf1.mul hg1
  · simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply,
      sub_eq_zero] at hf2 hg2 ⊢
    intro l j hlj
    rw [map_mul, map_mul, hf2 l j hlj, hg2 l j hlj]

theorem nu_eq {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg)
    (t : Fin N) :
    (∑ i : Fin n, ((aa h lam sg i).toNat * (if t.1 < i.1 + 1 then 1 else 0) +
      (bb h lam sg i).toNat * (if t.1 < i.1 + 1 then 1 else 0)) : ℕ) = lam.natW t := by
  subst h
  set ℓ : ℕ → ℤ := fun k => if hk : k < n + 1 then lam.w ⟨k, hk⟩ else 0 with hℓ
  apply Nat.cast_injective (R := ℤ)
  have hnat : ((lam.natW t : ℕ) : ℤ) = lam.w t - lam.w ⟨n, by omega⟩ := by
    have hle : t ≤ ⟨n, by omega⟩ := by rw [Fin.le_def]; have := t.2; simp; omega
    have := lam.anti hle
    simp only [DomWeight.natW, DomWeight.detShift, dif_pos (show 0 < n + 1 by omega)]
    rw [Int.toNat_of_nonneg (by simp; omega)]
    simp
  rw [hnat]
  push_cast
  rw [Finset.sum_congr rfl (g := fun i : Fin n => (fun k : ℕ => if t.1 ≤ k then ℓ k - ℓ (k + 1) else 0) i.1)]
  · rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => if t.1 ≤ k then ℓ k - ℓ (k + 1) else 0) n,
      XiA.tele_sum ℓ n t.1 (by have := t.2; omega)]
    simp only [hℓ, dif_pos t.2, dif_pos (show n < n + 1 by omega)]
  · intro i _
    have hi := i.2
    have hA : 0 ≤ aa rfl lam sg i := by have := (hI i).2; unfold aa; omega
    have hB : 0 ≤ bb rfl lam sg i := by have := (hI i).1; unfold bb; omega
    rw [Int.toNat_of_nonneg hA, Int.toNat_of_nonneg hB]
    simp only [hℓ, dif_pos (show i.1 < n + 1 by omega), dif_pos (show i.1 + 1 < n + 1 by omega)]
    by_cases hti : t.1 ≤ i.1
    · rw [if_pos (by omega), if_pos hti]
      unfold aa bb
      ring
    · rw [if_neg (by omega), if_neg hti]
      ring

theorem xi_mem {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) (hI : Interlace h lam sg) :
    xi ℂ h lam sg ∈ nablaSq ℂ N lam := by
  unfold nablaSq
  have key : lam.natW = ∑ i : Fin n, ((aa h lam sg i).toNat • (fun t : Fin N => if t.1 < i.1 + 1 then 1 else 0) +
      (bb h lam sg i).toNat • (fun t : Fin N => if t.1 < i.1 + 1 then 1 else 0)) := by
    funext t
    rw [← nu_eq h lam sg hI t]
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  unfold xi
  rw [key]
  refine XiA.prod_mem Finset.univ _ _ (fun i _ => ?_)
  apply mul_mem_dualWeyl_complex_add
  · apply XiA.pow_mem
    rw [XiA.lpMinor_eq]
    exact XiA.initMinor_mem _ _
  · apply XiA.pow_mem
    exact XiA.initMinor_mem _ _

theorem initMinor_ne {N s : ℕ} (I : Fin s → Fin N) (hI : Function.Injective I) (hs : s ≤ N) :
    Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) I hs ≠ 0 := by
  classical
  intro h0
  let v : Fin N × Fin N → ℂ := fun w => if ∃ p : Fin s, I p = w.1 ∧ Fin.castLE hs p = w.2 then 1 else 0
  have h1 := congrArg (MvPolynomial.eval v) h0
  rw [map_zero] at h1
  unfold Formalism.GradedWeylDivisibility.initMinor at h1
  rw [RingHom.map_det] at h1
  have hM : (MvPolynomial.eval v).mapMatrix
      (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs q) : MvPolynomial (Fin N × Fin N) ℂ)) = 1 := by
    ext p q
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, MvPolynomial.eval_X,
      Matrix.one_apply, v]
    by_cases hpq : p = q
    · subst hpq
      rw [if_pos ⟨p, rfl, rfl⟩, if_pos rfl]
    · rw [if_neg hpq, if_neg]
      rintro ⟨p', h2, h3⟩
      have h4 : p' = p := hI h2
      subst h4
      apply hpq
      have h5 := congrArg Fin.val h3
      simp only [Fin.coe_castLE] at h5
      exact Fin.ext h5
  rw [hM, Matrix.det_one] at h1
  exact one_ne_zero h1

theorem xi_ne {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n) : xi ℂ h lam sg ≠ 0 := by
  unfold xi
  rw [Finset.prod_ne_zero_iff]
  intro i _
  apply mul_ne_zero
  · apply pow_ne_zero
    rw [XiA.lpMinor_eq]
    exact initMinor_ne _ (Fin.castLE_injective _) _
  · apply pow_ne_zero
    exact initMinor_ne _ (XiA.rowsZ_strictMono h i).injective _

theorem eval_initMinor_norm_le {N s : ℕ} (x : Matrix (Fin N) (Fin N) ℂ) (hx : x ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (I : Fin s → Fin N) (hI : Function.Injective I) (hs : s ≤ N) :
    ‖MvPolynomial.eval (fun v : Fin N × Fin N => x v.1 v.2) (Formalism.GradedWeylDivisibility.initMinor ℂ (n := N) I hs)‖ ≤ 1 := by
  unfold Formalism.GradedWeylDivisibility.initMinor
  rw [RingHom.map_det]
  have : (MvPolynomial.eval fun v : Fin N × Fin N => x v.1 v.2).mapMatrix
      (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs q) : MvPolynomial (Fin N × Fin N) ℂ)) =
      Matrix.of fun p q => x (I p) (Fin.castLE hs q) := by
    ext p q; simp
  rw [this]
  exact XiU.det_sub_norm_le_one x hx I (Fin.castLE hs) hI (Fin.castLE_injective hs)

theorem xi_unitary {n N : ℕ} (h : n + 1 = N) (lam : DomWeight N) (sg : DomWeight n)
    (x : Matrix (Fin N) (Fin N) ℂ) (hx : x ∈ Matrix.unitaryGroup (Fin N) ℂ) :
    ‖MvPolynomial.eval (fun v : Fin N × Fin N => x v.1 v.2) (xi ℂ h lam sg)‖ ≤ 1 := by
  unfold xi
  rw [map_prod, norm_prod]
  apply Finset.prod_le_one (fun i _ => norm_nonneg _)
  intro i _
  rw [map_mul, map_pow, map_pow, norm_mul, norm_pow, norm_pow]
  apply mul_le_one₀ (pow_le_one₀ (norm_nonneg _) ?_) (pow_nonneg (norm_nonneg _) _)
    (pow_le_one₀ (norm_nonneg _) ?_)
  · rw [XiA.lpMinor_eq]
    exact eval_initMinor_norm_le x hx _ (Fin.castLE_injective _) _
  · exact eval_initMinor_norm_le x hx _ (XiA.rowsZ_strictMono h i).injective _

end PI.WGL.XiB
