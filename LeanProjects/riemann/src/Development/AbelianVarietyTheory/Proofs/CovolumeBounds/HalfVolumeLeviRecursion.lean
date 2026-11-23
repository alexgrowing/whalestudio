import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsKMeas
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelLiftBasics.LevelGroupUnitaryHermitian
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ParabolicLineStabilizerLeviStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.KsetTransitiveStatement

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 GlobalTheory.HCXi
open scoped ENNReal ComplexOrder

noncomputable section

namespace GlobalTheory.HCXi.VLev

theorem det_gram_cons {n m : ℕ} (e : Fin n → ℂ) (he : star e ⬝ᵥ e = 1) (w : Fin m → Fin n → ℂ)
    (hw : ∀ b, star e ⬝ᵥ w b = 0) (a : ℂ) (c : Fin m → ℂ) (v : Fin (m + 1) → Fin n → ℂ)
    (h0 : v 0 = a • e) (hs : ∀ b, v b.succ = w b + c b • e) :
    (Matrix.of fun i j => star (v i) ⬝ᵥ v j).det =
      (Complex.normSq a : ℂ) * (Matrix.of fun i j => star (w i) ⬝ᵥ w j).det := by
  have hw' : ∀ b, star (w b) ⬝ᵥ e = 0 := fun b => by
    rw [star_dotProduct, hw, star_zero]
  let u : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
    Matrix.of fun i j => (Fin.cons (α := fun _ => ℂ) (Fin.cons (α := fun _ => ℂ) a c j) (fun i' => if i'.succ = j then 1 else 0) i)
  let D : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
    Matrix.of fun i j => star (Fin.cons (α := fun _ => Fin n → ℂ) e w i) ⬝ᵥ (Fin.cons (α := fun _ => Fin n → ℂ) e w j)
  have hu : u.det = a := by
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ, Finset.sum_eq_zero]
    · have : u.submatrix (Fin.succAbove 0) Fin.succ = 1 := by
        ext i j
        simp [u, Matrix.one_apply]
      rw [this]; simp [u]
    · intro i _
      simp [u]
  have hD : D.det = (Matrix.of fun i j => star (w i) ⬝ᵥ w j).det := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Finset.sum_eq_zero]
    · have : D.submatrix Fin.succ (Fin.succAbove 0) = Matrix.of fun i j => star (w i) ⬝ᵥ w j := by
        ext i j
        simp [D]
      rw [this]; simp [D, he]
    · intro i _
      simp [D, hw]
  have hG : (Matrix.of fun i j => star (v i) ⬝ᵥ v j) = uᴴ * D * u := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [u, D, h0, hs, Matrix.mul_apply, Fin.sum_univ_succ, he, hw, hw', Matrix.conjTranspose_apply, mul_add, add_mul, Finset.sum_add_distrib,
        apply_ite (starRingEnd ℂ)] <;> ring
  rw [hG, det_mul, det_mul, det_conjTranspose, hu, hD, Complex.normSq_eq_conj_mul_self]
  simp only [Complex.star_def]; ring

theorem gram_eq (k r : ℕ) (g : Mat k r) (j : Fin (r + 1)) :
    gram k r g j = (Matrix.of fun i i' : Fin (j.val + 1) =>
      star (g *ᵥ fvec k r (isoVec k r) (Fin.castLE (Nat.succ_le_of_lt j.isLt) i)) ⬝ᵥ
        (g *ᵥ fvec k r (isoVec k r) (Fin.castLE (Nat.succ_le_of_lt j.isLt) i'))).det.re := by
  unfold gram
  congr 2

theorem gram_nonneg (k r : ℕ) (g : Mat k r) (j : Fin (r + 1)) : 0 ≤ gram k r g j := by
  unfold gram
  have := ((Matrix.posSemidef_conjTranspose_mul_self (g * frame k r)).submatrix
    (Fin.castLE (Nat.succ_le_of_lt j.isLt))).det_nonneg
  exact (Complex.nonneg_iff.1 this).1

theorem gram_K (k r : ℕ) (κ g : Mat k r) (hκ : κᴴ * κ = 1) (j : Fin (r + 1)) :
    gram k r (κ * g) j = gram k r g j := by
  unfold gram
  have : (κ * g * frame k r)ᴴ * (κ * g * frame k r) = (g * frame k r)ᴴ * (g * frame k r) := by
    rw [Matrix.mul_assoc κ, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc κᴴ, hκ, Matrix.one_mul]
  rw [this]

theorem fvec_zero (k r' : ℕ) (j : Fin (1 + r' + 1)) (hj : j.val = 0) :
    fvec k (1 + r') (isoVec k (1 + r')) j = e0 k r' := by
  unfold fvec e0
  rw [dif_pos (by omega)]
  congr 1
  ext; simp [eI, a0, hj]

theorem liftVec_add' (k i r' : ℕ) (v w : Fin (2 * r' + k + 1) → ℂ) :
    liftVec k i r' (v + w) = liftVec k i r' v + liftVec k i r' w := by
  ext p; simp only [liftVec, Pi.add_apply]; split_ifs <;> simp

theorem liftVec_smul' (k i r' : ℕ) (c : ℂ) (v : Fin (2 * r' + k + 1) → ℂ) :
    liftVec k i r' (c • v) = c • liftVec k i r' v := by
  ext p; simp only [liftVec, Pi.smul_apply]; split_ifs <;> simp

theorem fvec_succ (k r' : ℕ) (j : Fin (1 + r' + 1)) (b : Fin (r' + 1)) (hj : j.val = b.val + 1) :
    fvec k (1 + r') (isoVec k (1 + r')) j = liftVec k 1 r' (fvec k r' (isoVec k r') b) := by
  unfold fvec
  by_cases hb : b.val < r'
  · rw [dif_pos (by omega), dif_pos hb]
    exact (PI.QnLevBasicsW.bvec_lift _ _ (by simp only [eI]; omega)).symm
  · rw [dif_neg (by omega), dif_neg hb]
    unfold isoVec
    rw [liftVec_smul', liftVec_add', PI.QnLevBasicsW.bvec_lift _ (wI k (1 + r') 0) (by simp only [wI]; omega),
      PI.QnLevBasicsW.bvec_lift _ (wI k (1 + r') (Fin.last k)) (by simp only [wI]; omega)]

theorem star_e0_dotProduct (k r' : ℕ) (v : Fin (2 * (1 + r') + k + 1) → ℂ) :
    star (e0 k r') ⬝ᵥ v = v (eI k (1 + r') (a0 r')) := by
  simp [e0, bvec]

theorem star_e0_dotProduct_self (k r' : ℕ) : star (e0 k r') ⬝ᵥ e0 k r' = 1 := by
  rw [star_e0_dotProduct]; simp [e0, bvec]

theorem star_e0_dotProduct_lift (k r' : ℕ) (w : Fin (2 * r' + k + 1) → ℂ) : star (e0 k r') ⬝ᵥ liftVec k 1 r' w = 0 := by
  rw [star_e0_dotProduct]; exact PI.QnLevBasicsW.liftVec_apply_out _ _ (by simp [eI, a0])

section
variable {k r' : ℕ} (M : Mat k (1 + r')) (h : Mat k r') (a : ℂ) (hM0 : M *ᵥ e0 k r' = a • e0 k r')
  (hM : ∀ w : Fin (2 * r' + k + 1) → ℂ, ∃ c : ℂ, M *ᵥ liftVec k 1 r' w = liftVec k 1 r' (h *ᵥ w) + c • e0 k r')
include hM0

theorem gram_zero (j : Fin (1 + r' + 1)) (hj : j.val = 0) : gram k (1 + r') M j = Complex.normSq a := by
  obtain ⟨j, hj'⟩ := j
  simp only at hj
  subst hj
  rw [gram_eq]
  rw [det_gram_cons (m := 0) (e0 k r') (star_e0_dotProduct_self k r') Fin.elim0 (fun b => b.elim0) a Fin.elim0 _
    (by rw [fvec_zero _ _ _ rfl, hM0]) (fun b => b.elim0)]
  simp

include hM
theorem gram_succ (j : Fin (1 + r' + 1)) (b : Fin (r' + 1)) (hj : j.val = b.val + 1) :
    gram k (1 + r') M j = Complex.normSq a * gram k r' h b := by
  obtain ⟨j, hj'⟩ := j
  simp only at hj
  subst hj
  choose c hc using hM
  rw [gram_eq, gram_eq]
  rw [det_gram_cons (m := b.val + 1) (e0 k r') (star_e0_dotProduct_self k r')
    (fun i => liftVec k 1 r' (h *ᵥ fvec k r' (isoVec k r') (Fin.castLE (Nat.succ_le_of_lt b.isLt) i)))
    (fun _ => star_e0_dotProduct_lift _ _ _) a
    (fun i => c (fvec k r' (isoVec k r') (Fin.castLE (Nat.succ_le_of_lt b.isLt) i))) _
    (by rw [fvec_zero _ _ _ rfl, hM0])
    (fun i => by rw [fvec_succ _ _ _ (Fin.castLE (Nat.succ_le_of_lt b.isLt) i) rfl, hc])]
  simp only [PI.QnLevBasicsW.dot_lift, Complex.re_ofReal_mul]

theorem vHalf_block (ha : a ≠ 0) : vHalf k (1 + r') M =
    Complex.normSq a ^ (-(((2 * (1 + r') + k : ℕ) : ℝ) / 2)) * vHalf k r' h := by
  have hN : 0 < Complex.normSq a := Complex.normSq_pos.2 ha
  unfold vHalf
  rw [Fin.prod_univ_add, Fin.prod_univ_one, gram_zero M a hM0 _ rfl,
    gram_succ M h a hM0 hM (Fin.last _) (Fin.last _) (by simp; omega),
    Finset.prod_congr rfl (fun (b : Fin r') _ => by
      rw [gram_succ M h a hM0 hM _ b.castSucc (by simp; omega), mul_inv]),
    Finset.prod_mul_distrib, Real.mul_rpow hN.le (gram_nonneg _ _ _ _)]
  have : Complex.normSq a ^ (-(((2 * (1 + r') + k : ℕ) : ℝ) / 2)) =
      (Complex.normSq a)⁻¹ * (Complex.normSq a)⁻¹ ^ r' * Complex.normSq a ^ (-((k : ℝ) / 2)) := by
    rw [← pow_succ', inv_pow, ← Real.rpow_natCast, ← Real.rpow_neg hN.le, ← Real.rpow_add hN]
    congr 1; push_cast; ring
  rw [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring
end

theorem sqLen_eq {n : ℕ} (v : Fin n → ℂ) : sqLen v = (star v ⬝ᵥ v).re := by
  simp only [sqLen, dotProduct, Complex.re_sum, Pi.star_apply, Complex.star_def,
    ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]

theorem levi_embedding_mulVec_e0 (k r' : ℕ) (y : Mat k r') : ιLev k 1 r' y *ᵥ e0 k r' = e0 k r' :=
  PI.QnLevBasicsW.col_fix y _ (fun b hb => by simp [eI, a0] at hb)

theorem parabolic_mulVec_e0_smul {k r' : ℕ} {p : Mat k (1 + r')} (hp : p ∈ Pset k (1 + r')) :
    ∃ a : ℂ, p *ᵥ e0 k r' = a • e0 k r' := by
  obtain ⟨-, u, hu, hpu⟩ := hp
  refine ⟨u 0 0, ?_⟩
  ext i
  have h1 := congrFun (congrFun hpu i) 0
  rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_succ (n := 1 + r'), Finset.sum_eq_zero (s := Finset.univ)
    (f := fun b : Fin (1 + r') => frame k (1 + r') i b.succ * u b.succ 0)
    (fun b _ => by rw [hu (show id (0 : Fin (1 + r' + 1)) < id b.succ from Fin.succ_pos b), mul_zero])] at h1
  simp only [frame, Matrix.of_apply, fvec_zero k r' 0 rfl, add_zero] at h1
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [h1, mul_comm]

theorem vHalf_level : ∀ k r' : ℕ, 1 ≤ k → ∀ x ∈ GV k (1 + r'), ∃ g₁ ∈ GV k r', ∀ y ∈ GV k r', vHalf k (1 + r') (x * ιLev k 1 r' y) = sqLen (x *ᵥ e0 k r') ^ (-(((2 * (1 + r') + k : ℕ) : ℝ) / 2)) * vHalf k r' (g₁ * y) := by
  intro k r' hk x hx
  obtain ⟨κ, hκ, p, hp, rfl⟩ := GlobalTheory.T.exists_mem_Kset_mul_mem_Pset_eq k (1 + r') hk x hx
  obtain ⟨a, ha⟩ := parabolic_mulVec_e0_smul hp
  obtain ⟨ha0, g₁, hg₁, hw⟩ := GlobalTheory.T.parabolic_line_stabilizer_levi k r' a p hp.1 ha
  refine ⟨g₁, hg₁, fun y _ => ?_⟩
  have h1 : vHalf k (1 + r') (κ * p * ιLev k 1 r' y) = vHalf k (1 + r') (p * ιLev k 1 r' y) := by
    simp only [vHalf, Matrix.mul_assoc κ, gram_K _ _ _ _ hκ.2]
  have h2 : sqLen ((κ * p) *ᵥ e0 k r') = Complex.normSq a := by
    rw [sqLen_eq, ← Matrix.mulVec_mulVec, ha, star_mulVec, ← dotProduct_mulVec, Matrix.mulVec_mulVec, hκ.2,
      Matrix.one_mulVec, star_smul, smul_dotProduct, dotProduct_smul, star_e0_dotProduct_self]
    simp [Complex.normSq_apply]
  rw [h1, h2]
  refine vHalf_block _ _ a ?_ (fun w => ?_) ha0
  · rw [← Matrix.mulVec_mulVec, levi_embedding_mulVec_e0, ha]
  · rw [← Matrix.mulVec_mulVec, PI.QnLevBasicsW.mulVec_lift, ← Matrix.mulVec_mulVec]
    exact hw _

end GlobalTheory.HCXi.VLev
