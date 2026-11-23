import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsSystem
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LowestWeightFunctionMulEq
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsOrthonormalOfLinearIndependent

open Matrix Complex NumberField MeasureTheory GlobalTheory GlobalTheory.SW GlobalTheory.ThFr ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.LowestBound

noncomputable def rowMix {r : ℕ} (k : ℕ) (Y : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun i j => if (i : ℕ) < k then Y i j else (1 : Matrix (Fin r) (Fin r) ℂ) i j

theorem det_rowMix {r : ℕ} (Y : Matrix (Fin r) (Fin r) ℂ) (k : Fin (r + 1)) :
    (rowMix k Y).det = lminor Y k := by
  have h := Nat.le_of_lt_succ k.isLt
  rw [Matrix.twoBlockTriangular_det (rowMix k Y) (fun i => (i : ℕ) < k) (fun i hi j hj => by
    have : i ≠ j := fun e => hi (e ▸ hj)
    simp [rowMix, hi, Matrix.one_apply_ne this])]
  have e1 : toSquareBlockProp (rowMix k Y) (fun i => ¬ (i : ℕ) < k) = 1 := by
    ext i j
    simp [toSquareBlockProp_def, rowMix, i.2, Matrix.one_apply, Subtype.ext_iff]
  rw [e1, det_one, mul_one, lminor,
    ← Matrix.det_submatrix_equiv_self (Fin.castLEquiv h)]
  congr 1
  ext i j
  simp [toSquareBlockProp_def, rowMix]

theorem norm_lminor_le {r p : ℕ} (h : p ≤ r) (Y : Matrix (Fin r) (Fin r) ℂ)
    (hY : Yᵀ * (Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) * Y.map (starRingEnd ℂ) =
      Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) (k : Fin (r + 1)) :
    ‖lminor Y k‖ ≤ ‖lminor Y ⟨p, Nat.lt_succ_of_le h⟩‖ := by
  have h1 := FramePotential.one_le_norm_lminor_sq h Y hY
  have h0 : lminor Y ⟨p, Nat.lt_succ_of_le h⟩ ≠ 0 := by
    intro e; rw [e] at h1; norm_num at h1
  set N := rowMix p Y with hN
  have hNd : N.det = lminor Y ⟨p, Nat.lt_succ_of_le h⟩ := det_rowMix Y ⟨p, Nat.lt_succ_of_le h⟩
  have hu : IsUnit N.det := isUnit_iff_ne_zero.2 (hNd ▸ h0)
  set N' : Matrix (Fin r) (Fin r) ℂ :=
    Matrix.of fun i j => if (i : ℕ) < p then (1 : Matrix (Fin r) (Fin r) ℂ) i j else Y i j with hN'
  have hNN : N'ᴴ * N' = Nᴴ * N := by
    ext a b
    have e := congrFun (congrFun hY b) a
    rw [Matrix.mul_apply] at e
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply] at e
    have e2 : (Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) b a =
        ∑ k, (1 : Matrix (Fin r) (Fin r) ℂ) k b * ((sgn p (k : ℕ) : ℝ) : ℂ) *
          conj ((1 : Matrix (Fin r) (Fin r) ℂ) k a) := by
      rw [Finset.sum_eq_single b (fun c _ hc => by simp [Matrix.one_apply_ne hc]) (by simp)]
      by_cases hab : b = a
      · subst hab; simp
      · simp [hab]
    rw [e2, ← sub_eq_zero, ← Finset.sum_sub_distrib] at e
    rw [Matrix.mul_apply, Matrix.mul_apply, eq_comm, ← sub_eq_zero, ← Finset.sum_sub_distrib, ← e]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : (k : ℕ) < p
    · simp [hN, hN', rowMix, sgn, hk, Matrix.conjTranspose_apply, mul_comm]
    · simp [hN, hN', rowMix, sgn, hk, Matrix.conjTranspose_apply, mul_comm]
      ring
  set U := N' * N⁻¹ with hU
  have hUU : Uᴴ * U = 1 := by
    rw [hU, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc N'ᴴ, hNN, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hu, Matrix.mul_one, ← conjTranspose_mul,
      Matrix.mul_nonsing_inv _ hu, conjTranspose_one]
  have hUU' : U * Uᴴ = 1 := mul_eq_one_comm.1 hUU
  have hrow : ∀ i, ∑ j, ‖U i j‖ ^ 2 = 1 := by
    intro i
    have e := congrFun (congrFun hUU' i) i
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at e
    simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.mul_conj'] at e
    exact_mod_cast e
  have hrow1 : ∀ i, ∑ j, ‖(N * N⁻¹) i j‖ ^ 2 = 1 := by
    intro i
    rw [Matrix.mul_nonsing_inv _ hu,
      Finset.sum_eq_single i (fun c _ hc => by simp [Matrix.one_apply_ne' hc]) (by simp)]
    simp
  have hM : ‖(rowMix k Y * N⁻¹).det‖ ≤ 1 := by
    refine (Hadamard.norm_det_le_prod_row _).trans_eq (Finset.prod_eq_one fun i _ => ?_)
    rw [Real.sqrt_eq_one]
    by_cases hi : ((i : ℕ) < k ↔ (i : ℕ) < p)
    · rw [← hrow1 i]
      simp only [Matrix.mul_apply, hN, rowMix, Matrix.of_apply, hi]
    · rw [← hrow i]
      have hi' : (i : ℕ) < k ↔ ¬ (i : ℕ) < p := by tauto
      simp only [hU, Matrix.mul_apply, hN', rowMix, Matrix.of_apply, hi', ite_not]
  rw [det_mul, det_rowMix, det_nonsing_inv, Ring.inverse_eq_inv', hNd, norm_mul, norm_inv,
    ← div_eq_mul_inv, div_le_one (norm_pos_iff.2 h0)] at hM
  exact hM

theorem norm_det_eq_one {r p : ℕ} (Y : Matrix (Fin r) (Fin r) ℂ)
    (hY : Yᵀ * (Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) * Y.map (starRingEnd ℂ) =
      Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) : ‖Y.det‖ = 1 := by
  have e := congrArg (fun M => ‖M.det‖) hY
  have e1 : ‖(Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)).det‖ = 1 := by
    rw [det_diagonal, norm_prod]
    refine Finset.prod_eq_one fun a _ => ?_
    unfold sgn; split_ifs <;> simp
  have e2 : (Y.map (starRingEnd ℂ)).det = conj Y.det := ((starRingEnd ℂ).map_det Y).symm
  simp only [det_mul, norm_mul, e1, e2, det_transpose, Complex.norm_conj, mul_one] at e
  nlinarith [norm_nonneg Y.det]

theorem prod_zpow_sub (t : ℕ → ℂ) (L : ℕ → ℤ) (r : ℕ) (ht : ∀ j < r, t j ≠ 0) :
    (∏ k ∈ Finset.range r, (∏ j ∈ Finset.range (k + 1), t j) ^ (L k - L (k + 1))) *
      (∏ j ∈ Finset.range r, t j) ^ L r = ∏ j ∈ Finset.range r, t j ^ L j := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h0 : ∏ j ∈ Finset.range (r + 1), t j ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun j hj => ht j (Finset.mem_range.1 hj)
    rw [Finset.prod_range_succ, mul_assoc, ← zpow_add₀ h0, sub_add_cancel,
      Finset.prod_range_succ t, mul_zpow, ← mul_assoc, ih fun j hj => ht j (by omega),
      Finset.prod_range_succ]

def ext0 {r : ℕ} (la : Fin r → ℤ) (j : ℕ) : ℤ := if h : j < r then la ⟨j, h⟩ else 0

noncomputable def minorProd {r : ℕ} (la : Fin r → ℤ) (Y : Matrix (Fin r) (Fin r) ℂ) : ℂ :=
  ∏ k : Fin r, lminor Y k.succ ^ (ext0 la k - ext0 la (k + 1))

theorem minorProd_scale {r : ℕ} (la : Fin r → ℤ) (Y Y' : Matrix (Fin r) (Fin r) ℂ) (t : Fin r → ℂ)
    (ht : ∀ i, t i ≠ 0) (h : ∀ k : Fin (r + 1), lminor Y' k =
      lminor Y k * ∏ j : Fin k, t (Fin.castLE (Nat.le_of_lt_succ k.isLt) j)) :
    minorProd la Y' = (∏ i, t i ^ la i) * minorProd la Y := by
  set s : ℕ → ℂ := fun j => if h : j < r then t ⟨j, h⟩ else 1 with hs
  have key := prod_zpow_sub s (ext0 la) r (fun j hj => by simp [hs, hj, ht])
  have e0 : ext0 la r = 0 := by simp [ext0]
  rw [e0, zpow_zero, mul_one, Finset.prod_range, Finset.prod_range] at key
  have e1 : ∏ i, t i ^ la i = ∏ i : Fin r, s i ^ ext0 la i :=
    Finset.prod_congr rfl fun i _ => by simp [hs, ext0]
  rw [e1, ← key, minorProd, minorProd, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [h, mul_zpow, mul_comm, Finset.prod_range]
  congr 2
  refine Finset.prod_congr rfl fun j _ => ?_
  have hj : (j : ℕ) < r := by have := j.isLt; have := k.isLt; simp only [Fin.val_succ] at *; omega
  simp only [hs, hj, dif_pos]
  rfl

theorem lminor_diagonal_mul {r : ℕ} (t : Fin r → ℂ) (Y : Matrix (Fin r) (Fin r) ℂ)
    (k : Fin (r + 1)) : lminor (Matrix.diagonal t * Y) k =
      lminor Y k * ∏ j : Fin k, t (Fin.castLE (Nat.le_of_lt_succ k.isLt) j) := by
  rw [lminor, lminor, mul_comm, ← det_diagonal, ← det_mul]
  congr 1
  ext a b
  simp [Matrix.diagonal_mul]

theorem extendByZero_antitone_off_break {r p : ℕ} (la : Fin r → ℤ)
    (h1 : ∀ i j : Fin r, i ≤ j → (j : ℕ) < p → la j ≤ la i)
    (h2 : ∀ i j : Fin r, p ≤ (i : ℕ) → i ≤ j → la j ≤ la i) {k : ℕ} (hk : k + 1 < r)
    (hp : k + 1 ≠ p) : 0 ≤ ext0 la k - ext0 la (k + 1) := by
  have hk' : k < r := by omega
  simp only [ext0, hk, hk', dif_pos, sub_nonneg]
  rcases lt_or_gt_of_ne hp with h | h
  · exact h1 _ _ (by simp [Fin.le_def]) h
  · exact h2 _ _ (by simp only; omega) (by simp [Fin.le_def])

theorem norm_minorProd_le {r p : ℕ} (h : p ≤ r) (la : Fin r → ℤ) (n : ℕ)
    (h1 : ∀ i j : Fin r, i ≤ j → (j : ℕ) < p → la j ≤ la i)
    (h2 : ∀ i j : Fin r, p ≤ (i : ℕ) → i ≤ j → la j ≤ la i)
    (h3 : ∀ i j : Fin r, (i : ℕ) < p → p ≤ (j : ℕ) → la i + n ≤ la j)
    (Y : Matrix (Fin r) (Fin r) ℂ)
    (hY : Yᵀ * (Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) * Y.map (starRingEnd ℂ) =
      Matrix.diagonal fun a : Fin r => ((sgn p (a : ℕ) : ℝ) : ℂ)) :
    ‖minorProd la Y‖ * ‖lminor Y ⟨p, Nat.lt_succ_of_le h⟩‖ ^ n ≤ 1 := by
  set δ := ‖lminor Y ⟨p, Nat.lt_succ_of_le h⟩‖ with hδ
  have hδ1 : 1 ≤ δ := by
    have := FramePotential.one_le_norm_lminor_sq h Y hY
    nlinarith [norm_nonneg (lminor Y ⟨p, Nat.lt_succ_of_le h⟩)]
  have hδ0 : 0 < δ := by linarith
  have hlast : ∀ k : Fin (r + 1), (k : ℕ) = r → ‖lminor Y k‖ = 1 := by
    intro k hk
    obtain rfl : k = Fin.last r := Fin.ext hk
    rw [← norm_det_eq_one Y hY]
    rfl
  set M : ℕ → ℤ := fun k => ext0 la (min k (r - 1)) with hM
  have hb : ‖minorProd la Y‖ ≤ δ ^ (M 0 - M r) := by
    have hz : ∀ s : Finset ℕ, ∀ g : ℕ → ℤ, δ ^ (∑ k ∈ s, g k) = ∏ k ∈ s, δ ^ g k := by
      intro s g
      induction s using Finset.induction_on with
      | empty => simp
      | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add₀ hδ0.ne', ih]
    rw [← Finset.sum_range_sub' M r, hz, Finset.prod_range, minorProd, norm_prod]
    refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun k _ => ?_
    have hk := k.isLt
    rw [norm_zpow]
    by_cases hk' : (k : ℕ) + 1 = r
    · rw [hlast _ hk', _root_.one_zpow]
      simp only [hM]
      rw [show min ((k : ℕ) + 1) (r - 1) = min (k : ℕ) (r - 1) by omega, sub_self, zpow_zero]
    simp only [hM]
    rw [show min ((k : ℕ) + 1) (r - 1) = k + 1 by omega, show min (k : ℕ) (r - 1) = k by omega]
    by_cases hp : (k : ℕ) + 1 = p
    · have : k.succ = ⟨p, Nat.lt_succ_of_le h⟩ := Fin.ext hp
      rw [this]
    · exact zpow_le_zpow_left₀ (extendByZero_antitone_off_break la h1 h2 (by omega) hp) (norm_nonneg _)
        (norm_lminor_le h Y hY _)
  refine (mul_le_mul_of_nonneg_right hb (by positivity)).trans ?_
  rw [← zpow_natCast, ← zpow_add₀ hδ0.ne']
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have : δ = 1 := by simp [hδ, lminor]
    simp [this]
  rcases h.eq_or_lt with rfl | hpr
  · have : δ = 1 := hlast _ rfl
    simp [this]
  refine zpow_le_one_of_nonpos₀ hδ1 ?_
  have := h3 ⟨0, by omega⟩ ⟨r - 1, by omega⟩ hp (by simp only; omega)
  have e1 : M 0 = la ⟨0, by omega⟩ := by simp [hM, ext0, show 0 < r by omega]
  have e2 : M r = la (⟨r - 1, by omega⟩ : Fin r) := by simp [hM, ext0, show r - 1 < r by omega]
  omega

theorem differentiable_lminor {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ}
    (A : Matrix (Fin r) (Fin r) ℂ) (τ : Ψ) (k : Fin (r + 1)) :
    Differentiable ℂ fun x : Frame Ψ r => lminor (A * mat x τ) k := by
  simp only [lminor, det_apply', submatrix_apply, Matrix.mul_apply, mat, Matrix.of_apply]
  fun_prop

theorem differentiableAt_prod {V ι : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (s : Finset ι)
    {g : ι → V → ℂ} {y : V} (h : ∀ i ∈ s, DifferentiableAt ℂ (g i) y) :
    DifferentiableAt ℂ (fun x => ∏ i ∈ s, g i x) y := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end GlobalTheory.LowestBound

theorem GlobalTheory.lowest_weight_function_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (q0 : ℕ) (hr : X.p0 + q0 = r) (n : ℕ) (c : X.Ψ → Fin q0 → ℕ) (c' : X.Ψ → Fin X.p0 → ℕ) (x₀ : Frame X.Ψ r), Even n → (∀ τ : X.Ψ, gram τ.1 X.Gm (mat x₀ τ) = sgnM X) → ∀ f : Frame X.Ψ r → ℂ, DifferentiableOn ℂ f X.dom → (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, f (rmul x b) = bchar (wtOf X hr c c' n) b * f x) → (∀ t : X.Ψ → Fin r → ℂ, (∀ τ i, ‖t τ i‖ = 1) → ∀ x ∈ X.dom, f (X.lmulC (fun τ => mat x₀ τ * Matrix.diagonal (t τ) * (mat x₀ τ)⁻¹) x) = (∏ τ, ∏ i, t τ i ^ wtOf X hr c c' n τ i) * f x) → ∀ x : Frame X.Ψ r, (∀ τ : X.Ψ, gram τ.1 X.Gm (mat x τ) = sgnM X) → ‖f x‖ * ∏ τ, ‖lminor ((mat x₀ τ)⁻¹ * mat x τ) ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ ^ n ≤ ‖f x₀‖ := by
  intro E _ _ _ r X q0 hr n c c' x₀ hn hx₀ f hf hB hT x hx
  have hdom : ∀ {y : Frame X.Ψ r}, AR.Up.IsOrth X y → y ∈ X.dom := by
    intro y ho
    refine AR.Up.ExF.mem_dom_of_gramPos X fun τ => ⟨AR.Up.ExF.det_ne_of_orth X ho τ, ?_⟩
    have e : X.gramPos y τ = 1 := by
      ext a b
      simp only [Data.gramPos, ho τ, Matrix.submatrix_apply, Matrix.diagonal_apply,
        Matrix.one_apply, Fin.castLE_inj]
      split_ifs <;> simp [sgn]
    rw [e]; exact Matrix.PosDef.one
  have h₀ : x₀ ∈ X.dom := hdom hx₀
  have hu : ∀ τ, IsUnit (mat x₀ τ).det := fun τ => isUnit_iff_ne_zero.2 (h₀ τ).1
  set la := wtOf X hr c c' n with hla
  have hd : X.IsDominant la := wtOf_isDominant X hr c c' n
  set m : Frame X.Ψ r → ℂ :=
    fun y => ∏ τ, LowestBound.minorProd (la τ) ((mat x₀ τ)⁻¹ * mat y τ) with hm
  have hm0 : m x₀ = 1 := by
    refine Finset.prod_eq_one fun τ _ => Finset.prod_eq_one fun k _ => ?_
    rw [Matrix.nonsing_inv_mul _ (hu τ), AR.Up.LUPf.lminor_one, _root_.one_zpow]
  have hmd : DifferentiableOn ℂ m X.dom := by
    intro y hy
    refine DifferentiableAt.differentiableWithinAt ?_
    simp only [hm, LowestBound.minorProd]
    refine LowestBound.differentiableAt_prod _ fun τ _ =>
      LowestBound.differentiableAt_prod _ fun k _ => ?_
    refine (LowestBound.differentiable_lminor _ τ _ y).zpow ?_
    by_cases hk : (k : ℕ) + 1 = X.p0
    · left
      have : k.succ = ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ := Fin.ext hk
      rw [this]
      exact Up.lminor_inv_mul_ne_zero hx₀ hy τ
    by_cases hk' : (k : ℕ) + 1 = r
    · left
      have : k.succ = Fin.last r := Fin.ext hk'
      rw [this]
      change ((mat x₀ τ)⁻¹ * mat y τ).det ≠ 0
      rw [det_mul, det_nonsing_inv, Ring.inverse_eq_inv']
      exact mul_ne_zero (inv_ne_zero (h₀ τ).1) (hy τ).1
    · right
      exact LowestBound.extendByZero_antitone_off_break _ (hd τ).1 (hd τ).2.1 (by have := k.isLt; omega) hk
  have key := lowest_weight_function_mul_eq X la x₀ hx₀ h₀ f m hf hmd hB (fun y _ b hb => ?_) hT
    (fun t ht y _ => ?_) x (hdom hx)
  · rw [hm0, mul_one] at key
    rw [key, norm_mul, mul_right_comm]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    rw [hm, norm_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_one (fun τ _ => by positivity) fun τ _ => ?_
    refine LowestBound.norm_minorProd_le X.p0_le (la τ) n (hd τ).1 (hd τ).2.1 (fun i j hi hj => ?_)
      _ ?_
    · obtain ⟨i | i, rfl⟩ := (rowIdx hr).surjective i <;>
        obtain ⟨j | j, rfl⟩ := (rowIdx hr).surjective j <;>
        have hi' := i.isLt <;> have hj' := j.isLt <;>
        simp only [rowIdx_inl, rowIdx_inr, hla, wtOf_inl, wtOf_inr] at hi hj ⊢ <;>
        obtain ⟨s, rfl⟩ := hn <;> omega
    · have e := FrameDegreeData.gram_mul τ.1 X.Gm (mat x₀ τ) ((mat x₀ τ)⁻¹ * mat x τ)
      rw [Matrix.mul_nonsing_inv_cancel_left _ _ (hu τ), hx τ, hx₀ τ] at e
      exact e.symm
  · simp only [hm, bchar]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    refine LowestBound.minorProd_scale _ _ _ (fun i => b τ i i) (FrameDegreeData.bdiag_ne X hb τ) fun k => ?_
    change lminor ((mat x₀ τ)⁻¹ * (mat y τ * mat b τ)) k = _
    rw [← Matrix.mul_assoc, FramePotential.lminor_mul_upper _ (FrameDegreeData.upper_of_bor X hb τ)]
    rfl
  · simp only [hm]
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    refine LowestBound.minorProd_scale _ _ _ (t τ)
      (fun i => norm_ne_zero_iff.1 (by rw [ht τ i]; exact one_ne_zero)) fun k => ?_
    change lminor ((mat x₀ τ)⁻¹ * (mat x₀ τ * Matrix.diagonal (t τ) * (mat x₀ τ)⁻¹ * mat y τ)) k = _
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ (hu τ),
      LowestBound.lminor_diagonal_mul]
