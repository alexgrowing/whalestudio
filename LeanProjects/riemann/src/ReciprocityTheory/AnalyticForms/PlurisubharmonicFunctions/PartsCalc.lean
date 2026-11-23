import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsAlg
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul

namespace ReciprocityTheory.AnForm.A

open MeasureTheory ReciprocityTheory.AnForm Matrix

noncomputable section

theorem integrable_fderiv_apply_of_cs {D : ℕ} {g : (Fin D → ℂ) → ℂ} (hg : ContDiff ℝ 1 g)
    (hcs : HasCompactSupport g) (u : Fin D → ℂ) : Integrable (fun z => fderiv ℝ g z u) := by
  have hc : Continuous fun z => fderiv ℝ g z u :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  refine hc.integrable_of_hasCompactSupport ?_
  exact (hcs.fderiv ℝ).mono fun z hz h0 => hz (by simp [h0])

theorem integral_fderiv_apply_of_cs {D : ℕ} {g : (Fin D → ℂ) → ℂ} (hg : ContDiff ℝ 1 g)
    (hcs : HasCompactSupport g) (u : Fin D → ℂ) : ∫ z, fderiv ℝ g z u = 0 := by
  have hd := hg.differentiable one_ne_zero
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun _ : Fin D → ℂ => (1 : ℂ)) (g := g) (v := u)
    (by simp) (by simpa using integrable_fderiv_apply_of_cs hg hcs u)
    (by simpa using (hg.continuous.integrable_of_hasCompactSupport hcs))
    (fun x _ => differentiableAt_const _) (fun x _ => hd x)
  simpa using h

theorem integral_dz_formula : IntegralDzStatement := by
  intro D j g hg hcs
  have h1 := integrable_fderiv_apply_of_cs hg hcs (Pi.single j 1)
  have h2 := integrable_fderiv_apply_of_cs hg hcs (Complex.I • Pi.single j 1)
  have i1 := integral_fderiv_apply_of_cs hg hcs (Pi.single j 1)
  have i2 := integral_fderiv_apply_of_cs hg hcs (Complex.I • Pi.single j 1)
  constructor
  · unfold dz
    rw [integral_div, integral_sub h1 (h2.const_mul _), integral_const_mul, i1, i2]
    simp
  · unfold dzb
    rw [integral_div, integral_add h1 (h2.const_mul _), integral_const_mul, i1, i2]
    simp

theorem mixedDisc_transpose {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    mdisc (fun k => (A k)ᵀ) = mdisc A := by
  unfold mdisc
  congr 1
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [← Matrix.transpose_sum, Matrix.det_transpose]

theorem mdisc_swap_row {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (p q : Fin D) (hpq : p ≠ q)
    (j k a b : Fin D) :
    mdisc (Function.update (Function.update A p (Matrix.single j k 1)) q (Matrix.single a b 1)) =
      - mdisc (Function.update (Function.update A p (Matrix.single a k 1)) q
          (Matrix.single j b 1)) := by
  have hu : ∀ (X Y : Matrix (Fin D) (Fin D) ℂ) r, Function.update (Function.update A p X) q Y r =
      if r = q then Y else if r = p then X else A r := by
    intro X Y r
    simp only [Function.update_apply]
  rw [mdisc_eq_sum_perm, mdisc_eq_sum_perm, ← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  by_cases h1 : σ k = p
  · by_cases h2 : σ b = q
    · have hkb : k ≠ b := fun h => hpq (h1.symm.trans (h ▸ h2))
      have hM : (Matrix.of fun i c => Function.update (Function.update A p (Matrix.single a k 1)) q
          (Matrix.single j b 1) (σ c) i c) = (Matrix.of fun i c => Function.update (Function.update A p
          (Matrix.single j k 1)) q (Matrix.single a b 1) (σ c) i c).submatrix id (Equiv.swap k b) := by
        ext i c
        simp only [Matrix.of_apply, Matrix.submatrix_apply, id, hu]
        by_cases hck : c = k
        · rw [hck, Equiv.swap_apply_left, h1, h2]
          simp [hpq, Ne.symm hpq, Matrix.single_apply]
        · by_cases hcb : c = b
          · rw [hcb, Equiv.swap_apply_right, h1, h2]
            simp [hpq, Ne.symm hpq, Matrix.single_apply]
          · rw [Equiv.swap_apply_of_ne_of_ne hck hcb]
            have hp : σ c ≠ p := fun h => hck (σ.injective (h.trans h1.symm))
            have hq : σ c ≠ q := fun h => hcb (σ.injective (h.trans h2.symm))
            simp [hp, hq]
      rw [hM, Matrix.det_permute', Equiv.Perm.sign_swap hkb]
      simp
    · have hbq : b ≠ σ.symm q := fun h => h2 (by rw [h, Equiv.apply_symm_apply])
      rw [Matrix.det_eq_zero_of_column_eq_zero (σ.symm q) fun i => by
          simp [hu, Matrix.single_apply, hbq],
        Matrix.det_eq_zero_of_column_eq_zero (σ.symm q) fun i => by
          simp [hu, Matrix.single_apply, hbq], neg_zero]
  · have hkp : k ≠ σ.symm p := fun h => h1 (by rw [h, Equiv.apply_symm_apply])
    rw [Matrix.det_eq_zero_of_column_eq_zero (σ.symm p) fun i => by
        simp [hu, Matrix.single_apply, hkp, hpq],
      Matrix.det_eq_zero_of_column_eq_zero (σ.symm p) fun i => by
        simp [hu, Matrix.single_apply, hkp, hpq], neg_zero]

abbrev BilinSp (D : ℕ) := (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ

def evalL {D : ℕ} (x w : Fin D → ℂ) : BilinSp D →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ w).comp (ContinuousLinearMap.apply ℝ ((Fin D → ℂ) →L[ℝ] ℝ) x)

theorem evalL_apply {D : ℕ} (x w : Fin D → ℂ) (H : BilinSp D) : evalL x w H = H x w := rfl

def hessEntry {D : ℕ} (a b : Fin D) : BilinSp D →L[ℝ] ℂ :=
  (1 / 4 : ℂ) • (Complex.ofRealCLM.comp
      (evalL (Pi.single a 1) (Pi.single b 1) +
        evalL (Complex.I • Pi.single a 1) (Complex.I • Pi.single b 1)) +
    Complex.I • Complex.ofRealCLM.comp
      (evalL (Pi.single a 1) (Complex.I • Pi.single b 1) -
        evalL (Complex.I • Pi.single a 1) (Pi.single b 1)))

theorem hessEntry_apply {D : ℕ} (a b : Fin D) (H : BilinSp D) :
    hessEntry a b H =
      ((H (Pi.single a 1) (Pi.single b 1) +
          H (Complex.I • Pi.single a 1) (Complex.I • Pi.single b 1) : ℝ) +
        Complex.I * ((H (Pi.single a 1) (Complex.I • Pi.single b 1) -
          H (Complex.I • Pi.single a 1) (Pi.single b 1) : ℝ))) / 4 := by
  simp only [hessEntry, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, evalL_apply,
    smul_eq_mul]
  push_cast
  ring

def hessMat {D : ℕ} : BilinSp D →ₗ[ℝ] Matrix (Fin D) (Fin D) ℂ where
  toFun H := Matrix.of fun a b => hessEntry a b H
  map_add' H K := by ext a b; simp
  map_smul' c H := by ext a b; simp

theorem hessMat_apply {D : ℕ} (H : BilinSp D) (a b : Fin D) : hessMat H a b = hessEntry a b H := rfl

theorem hessC_eq_hessMat {D : ℕ} (φ : (Fin D → ℂ) → ℝ) (y : Fin D → ℂ) :
    hessC φ y = hessMat (fderiv ℝ (fderiv ℝ φ) y) := by
  ext a b
  rw [hessMat_apply, hessEntry_apply]
  rfl

theorem continuous_mdisc {D : ℕ} :
    Continuous (fun A : Fin D → Matrix (Fin D) (Fin D) ℂ => mdisc A) := by
  unfold mdisc
  refine continuous_const.mul (continuous_finset_sum _ fun S _ => continuous_const.mul ?_)
  exact (continuous_finset_sum _ fun k _ => continuous_apply k).matrix_det

theorem hessCof_eq {n : ℕ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (y : Fin (n + 1) → ℂ) (j k : Fin (n + 1)) :
    hessCof φ y j k = mdisc (Fin.cons (Matrix.single j k 1) fun i => hessMat (fderiv ℝ (fderiv ℝ (φ i)) y)) := by
  simp only [hessCof, mixedCof, hessC_eq_hessMat]

private theorem exists_continuousMultilinearMap_eq_mdisc (D : ℕ) :
    ∃ Mc : ContinuousMultilinearMap ℝ (fun _ : Fin D => Fin D → Fin D → ℂ) ℂ,
      ∀ x : Fin D → Matrix (Fin D) (Fin D) ℂ, Mc x = mdisc x := by
  obtain ⟨M, hM⟩ := exists_multilinearMap_eq_mdisc (D := D)
  let Mr : MultilinearMap ℝ (fun _ : Fin D => Fin D → Fin D → ℂ) ℂ := M.restrictScalars ℝ
  have hMr : ∀ x : Fin D → Matrix (Fin D) (Fin D) ℂ, Mr x = mdisc x := fun x => congrFun hM x
  exact ⟨⟨Mr, by
    have : (⇑Mr : (Fin D → Fin D → Fin D → ℂ) → ℂ) = fun x => mdisc x := funext hMr
    show Continuous (⇑Mr)
    rw [this]
    exact continuous_mdisc⟩, hMr⟩

theorem hessCof_hasDeriv {n : ℕ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (z : Fin (n + 1) → ℂ)
    (hφ : ∀ i, DifferentiableAt ℝ (fderiv ℝ (fderiv ℝ (φ i))) z) (j k : Fin (n + 1)) :
    DifferentiableAt ℝ (fun y => hessCof φ y j k) z ∧ ∀ u,
      fderiv ℝ (fun y => hessCof φ y j k) z u = ∑ i, mdisc (Function.update
        (Fin.cons (Matrix.single j k 1) fun l => hessC (φ l) z) i.succ
          (hessMat (fderiv ℝ (fderiv ℝ (fderiv ℝ (φ i))) z u))) := by
  obtain ⟨Mc, hMc⟩ := exists_continuousMultilinearMap_eq_mdisc (n + 1)
  let Lℓ : BilinSp (n + 1) →ₗ[ℝ] (Fin (n + 1) → Fin (n + 1) → ℂ) := hessMat
  let L : BilinSp (n + 1) →L[ℝ] (Fin (n + 1) → Fin (n + 1) → ℂ) := LinearMap.toContinuousLinearMap Lℓ
  let g : (Fin (n + 1) → ℂ) → (Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℂ) :=
    fun y => Fin.cons (Matrix.single j k (1 : ℂ) : Fin (n + 1) → Fin (n + 1) → ℂ)
      fun l => L (fderiv ℝ (fderiv ℝ (φ l)) y)
  let g' : (Fin (n + 1) → ℂ) →L[ℝ] (Fin (n + 1) → Fin (n + 1) → Fin (n + 1) → ℂ) :=
    ContinuousLinearMap.pi fun i =>
      Fin.cases 0 (fun l => L.comp (fderiv ℝ (fderiv ℝ (fderiv ℝ (φ l))) z)) i
  have hg : HasFDerivAt g g' z := by
    refine hasFDerivAt_pi.2 fun i => ?_
    refine Fin.cases ?_ (fun l => ?_) i
    · simp only [g, g', Fin.cons_zero, Fin.cases_zero]
      exact hasFDerivAt_const _ _
    · simp only [g, g', Fin.cons_succ, Fin.cases_succ]
      exact L.hasFDerivAt.comp z (hφ l).hasFDerivAt
  have hfun : (fun y => hessCof φ y j k) = fun y => Mc (g y) := by
    funext y
    rw [hessCof_eq, ← hMc]
    rfl
  have hD : HasFDerivAt (fun y => Mc (g y)) ((Mc.linearDeriv (g z)).comp g') z :=
    (Mc.hasFDerivAt (g z)).comp z hg
  rw [hfun]
  refine ⟨hD.differentiableAt, fun u => ?_⟩
  rw [hD.fderiv, ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.linearDeriv_apply,
    Fin.sum_univ_succ]
  have h0 : g' u 0 = 0 := by simp [g']
  have hz : Mc (Function.update (g z) 0 (g' u 0)) = 0 := by
    rw [h0]
    exact Mc.toMultilinearMap.map_update_zero _ _
  rw [hz, zero_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hMc]
  congr 1
  funext r
  by_cases hr : r = i.succ
  · rw [hr, Function.update_self, Function.update_self]
    simp only [g', ContinuousLinearMap.pi_apply, Fin.cases_succ, ContinuousLinearMap.comp_apply]
    rfl
  · rw [Function.update_of_ne hr, Function.update_of_ne hr]
    refine Fin.cases ?_ (fun l => ?_) r
    · rfl
    · simp only [g, Fin.cons_succ]
      rw [hessC_eq_hessMat]
      rfl

theorem mdisc_update_comb {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (q : Fin D) (c d : ℂ)
    (B C : Matrix (Fin D) (Fin D) ℂ) :
    mdisc (Function.update A q (c • B + d • C)) =
      c * mdisc (Function.update A q B) + d * mdisc (Function.update A q C) := by
  rw [mdisc_update_add, mdisc_update_smul, mdisc_update_smul]

theorem mdisc_update_expand {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (q : Fin D)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    mdisc (Function.update A q X) =
      ∑ a, ∑ b, X a b * mdisc (Function.update A q (Matrix.single a b 1)) := by
  obtain ⟨M, hM⟩ := exists_multilinearMap_eq_mdisc (D := D)
  have hX : X = ∑ a, ∑ b, X a b • Matrix.single a b (1 : ℂ) := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul, mul_ite, mul_one,
      mul_zero]
    rw [Finset.sum_eq_single i (fun c _ hc => by simp [hc]) (by simp),
      Finset.sum_eq_single j (fun c _ hc => by simp [hc]) (by simp)]
    simp
  have h : ∀ Y, mdisc (Function.update A q Y) = M.toLinearMap A q Y := fun Y => by
    rw [MultilinearMap.toLinearMap_apply, hM]
  rw [h]
  conv_lhs => rw [hX]
  simp only [map_sum, map_smul, smul_eq_mul]
  simp only [← h]

theorem mdisc_sum_row {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (p q : Fin D) (hpq : p ≠ q)
    (k : Fin D) (S : Fin D → Matrix (Fin D) (Fin D) ℂ) (hS : ∀ j a b, S j a b = S a j b) :
    ∑ j, mdisc (Function.update (Function.update A p (Matrix.single j k 1)) q (S j)) = 0 := by
  rw [Finset.sum_congr rfl fun j _ => mdisc_update_expand _ q (S j)]
  have h2 : ∑ j, ∑ a, ∑ b, S j a b * mdisc (Function.update (Function.update A p (Matrix.single j k 1)) q
      (Matrix.single a b 1)) = -∑ j, ∑ a, ∑ b, S j a b * mdisc (Function.update
      (Function.update A p (Matrix.single j k 1)) q (Matrix.single a b 1)) := by
    conv_lhs => rw [Finset.sum_comm]
    simp only [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun a _ =>
      Finset.sum_congr rfl fun b _ => ?_
    rw [hS a j b, mdisc_swap_row A p q hpq j k a b]
    ring
  linear_combination (1 / 2 : ℂ) * h2

theorem update_transpose {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (p q : Fin D)
    (X Y : Matrix (Fin D) (Fin D) ℂ) :
    (fun r => (Function.update (Function.update A p X) q Y r)ᵀ) =
      Function.update (Function.update (fun r => (A r)ᵀ) p Xᵀ) q Yᵀ := by
  funext r
  simp only [Function.update_apply]
  split_ifs <;> rfl

theorem mdisc_sum_col {D : ℕ} (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (p q : Fin D) (hpq : p ≠ q)
    (j : Fin D) (S : Fin D → Matrix (Fin D) (Fin D) ℂ) (hS : ∀ k a b, S k a b = S b a k) :
    ∑ k, mdisc (Function.update (Function.update A p (Matrix.single j k 1)) q (S k)) = 0 := by
  have ht : ∀ k', mdisc (Function.update (Function.update A p (Matrix.single j k' 1)) q (S k')) =
      mdisc (Function.update (Function.update (fun r => (A r)ᵀ) p (Matrix.single k' j 1)) q (S k')ᵀ) := by
    intro k'
    rw [← mixedDisc_transpose, update_transpose, Matrix.transpose_single]
  rw [Finset.sum_congr rfl fun k' _ => ht k']
  exact mdisc_sum_row (fun r => (A r)ᵀ) p q hpq j (fun k' => (S k')ᵀ)
    (fun x a b => by simp only [Matrix.transpose_apply]; exact hS x b a)

theorem exists_hessCof_multilinear (n : ℕ) (j k : Fin (n + 1)) :
    ∃ G : ContinuousMultilinearMap ℝ (fun _ : Fin n => BilinSp (n + 1)) ℂ,
      ∀ (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (y : Fin (n + 1) → ℂ),
        hessCof φ y j k = G (fun i => fderiv ℝ (fderiv ℝ (φ i)) y) := by
  obtain ⟨Mc, hMc⟩ := exists_continuousMultilinearMap_eq_mdisc (n + 1)
  let Lℓ : BilinSp (n + 1) →ₗ[ℝ] (Fin (n + 1) → Fin (n + 1) → ℂ) := hessMat
  let L : BilinSp (n + 1) →L[ℝ] (Fin (n + 1) → Fin (n + 1) → ℂ) := LinearMap.toContinuousLinearMap Lℓ
  refine ⟨(Mc.curryLeft (Matrix.single j k (1 : ℂ) : Fin (n + 1) → Fin (n + 1) → ℂ)).compContinuousLinearMap
    fun _ => L, fun φ y => ?_⟩
  rw [hessCof_eq, ← hMc]
  rfl

theorem hessCof_contDiffOn {n : ℕ} (φ : Fin n → (Fin (n + 1) → ℂ) → ℝ) (U : Set (Fin (n + 1) → ℂ))
    (hU : IsOpen U) (m : ℕ) (hφ : ∀ i, ContDiffOn ℝ (m + 2) (φ i) U) (j k : Fin (n + 1)) :
    ContDiffOn ℝ m (fun y => hessCof φ y j k) U := by
  obtain ⟨G, hG⟩ := exists_hessCof_multilinear n j k
  have h2 : ∀ i, ContDiffOn ℝ m (fun y => fderiv ℝ (fderiv ℝ (φ i)) y) U := fun i =>
    ((hφ i).fderiv_of_isOpen (m := ((m + 1 : ℕ) : WithTop ℕ∞)) hU
      (by exact_mod_cast (show m + 1 + 1 ≤ m + 2 by omega))).fderiv_of_isOpen hU
      (by exact_mod_cast (le_refl (m + 1)))
  have hc : ContDiffOn ℝ m (fun y => G (fun i => fderiv ℝ (fderiv ℝ (φ i)) y)) U :=
    G.contDiff.comp_contDiffOn (contDiffOn_pi.2 h2)
  have hfun : (fun y => hessCof φ y j k) = fun y => G (fun i => fderiv ℝ (fderiv ℝ (φ i)) y) :=
    funext fun y => hG φ y
  rw [hfun]
  exact hc

end

end ReciprocityTheory.AnForm.A
