import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatEqLowMat
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.ExhaustionFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBallMinorOne
open Matrix
open scoped ComplexOrder

theorem norm_det_le_add_rankOne {k : ℕ} (P : Matrix (Fin k) (Fin k) ℂ) (hP : P.PosSemidef)
    (v : Fin k → ℂ) (c : ℝ) (hc : 0 ≤ c) :
    ‖P.det‖ ≤ ‖(P + (c : ℂ) • (replicateCol (Fin 1) v * replicateRow (Fin 1) (star v))).det‖ := by
  by_cases hu : IsUnit P.det
  · have hPD : P.PosDef := hP.posDef_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det P).2 hu)
    have hinv : (P⁻¹).PosSemidef := hPD.inv.posSemidef
    have e : (c : ℂ) • (replicateCol (Fin 1) v * replicateRow (Fin 1) (star v)) =
        replicateCol (Fin 1) ((c : ℂ) • v) * replicateRow (Fin 1) (star v) := by
      ext i j; simp [Matrix.mul_apply, mul_assoc]
    have h1 : ((1 : Matrix (Fin 1) (Fin 1) ℂ) + replicateRow (Fin 1) (star v) * P⁻¹ *
        replicateCol (Fin 1) ((c : ℂ) • v)).det = 1 + (c : ℂ) * (star v ⬝ᵥ P⁻¹ *ᵥ v) := by
      rw [Matrix.det_fin_one]
      simp [Matrix.mul_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_comm, mul_left_comm, mul_assoc]
      rw [Finset.sum_comm]
    rw [e]
    erw [det_add_replicateCol_mul_replicateRow (ι := Fin 1) hu]
    rw [norm_mul]
    erw [h1]
    have hre : 0 ≤ (star v ⬝ᵥ P⁻¹ *ᵥ v).re := by
      have := hinv.re_dotProduct_nonneg v
      simpa using this
    have h2 : 1 ≤ ‖(1 : ℂ) + (c : ℂ) * (star v ⬝ᵥ P⁻¹ *ᵥ v)‖ := by
      refine le_trans ?_ (Complex.re_le_norm _)
      simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      nlinarith
    have h3 : 0 ≤ ‖P.det‖ := norm_nonneg _
    nlinarith
  · have : P.det = 0 := by simpa using hu
    rw [this, norm_zero]; exact norm_nonneg _

end GlobalTheory.IntBallMinorOne

namespace GlobalTheory.IntBallMinorOne
open Matrix
open scoped ComplexOrder

theorem schur_bound {m k : ℕ} (Z : Matrix (Fin m) (Fin 1) ℂ) (N : Matrix (Fin m) (Fin k) ℂ)
    (hd : 0 < (1 - Zᴴ * Z).det.re) :
    (1 - Zᴴ * Z).det.re * ‖(Nᴴ * N).det‖ ≤
      ‖((fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 Z N)ᴴ *
        fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 (-1 : Matrix (Fin m) (Fin m) ℂ) *
        fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 Z N).det‖ := by
  set d : Matrix (Fin 1) (Fin 1) ℂ := 1 - Zᴴ * Z with hdd
  have hprod : (fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 Z N)ᴴ *
        fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 0 (-1 : Matrix (Fin m) (Fin m) ℂ) *
        fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℂ) 0 Z N =
      fromBlocks d (-(Zᴴ * N)) (-(Nᴴ * Z)) (-(Nᴴ * N)) := by
    rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
    simp [hdd, sub_eq_add_neg, Matrix.neg_mul, Matrix.mul_neg]
  have hdet : d.det = d 0 0 := Matrix.det_fin_one d
  have hherm : d.IsHermitian := Matrix.isHermitian_one.sub (Matrix.isHermitian_conjTranspose_mul_self Z)
  have him : (d 0 0).im = 0 := by
    have := hherm.apply 0 0
    have h2 : (starRingEnd ℂ) (d 0 0) = d 0 0 := this
    exact Complex.conj_eq_iff_im.1 h2
  set δ : ℝ := d.det.re with hδ
  have hreal : d.det = (δ : ℂ) := by
    apply Complex.ext
    · simp [hδ]
    · simp [hdet, him]
  have hne : d.det ≠ 0 := by
    rw [hreal]; exact_mod_cast hd.ne'
  haveI : Invertible d := Matrix.invertibleOfIsUnitDet d (isUnit_iff_ne_zero.2 hne)
  have hinvd : ⅟d = (((δ : ℂ))⁻¹) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    rw [Matrix.invOf_eq_nonsing_inv]
    ext i j
    fin_cases i; fin_cases j
    simp [Matrix.inv_def, Matrix.adjugate_fin_one, hreal]
    rw [← hdet, hreal]
  rw [hprod, det_fromBlocks₁₁]
  set v : Fin k → ℂ := fun j => (Nᴴ * Z) j 0 with hv
  have hs : ∀ j, (Zᴴ * N) 0 j = star (v j) := by
    intro j
    simp only [hv, Matrix.mul_apply, Matrix.conjTranspose_apply, star_sum, star_mul', star_star]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have hcr : Nᴴ * Z * (Zᴴ * N) = replicateCol (Fin 1) v * replicateRow (Fin 1) (star v) := by
    ext i j
    rw [Matrix.mul_apply (M := Nᴴ * Z), Fin.sum_univ_one, hs j, Matrix.mul_apply (M := replicateCol (Fin 1) v),
      Fin.sum_univ_one]
    rfl
  have hrk : -(Nᴴ * N) - -(Nᴴ * Z) * ⅟d * -(Zᴴ * N) =
      -((Nᴴ * N) + ((δ⁻¹ : ℝ) : ℂ) • (replicateCol (Fin 1) v * replicateRow (Fin 1) (star v))) := by
    rw [hinvd, ← hcr]
    simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    push_cast
    module
  rw [hrk, Matrix.det_neg, norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, hreal,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd]
  gcongr
  exact norm_det_le_add_rankOne _ (Matrix.posSemidef_conjTranspose_mul_self N) v _
    (inv_nonneg.2 hd.le)

end GlobalTheory.IntBallMinorOne

namespace GlobalTheory.IntBallMinorOne
open Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem lowMat_diag (w : Low r → ℂ) (a : Fin r) : lowMat w a a = 1 := by
  simp [lowMat]

theorem lowMat_upper (w : Low r → ℂ) {a b : Fin r} (h : a < b) : lowMat w a b = 0 := by
  have h1 : ¬ b < a := fun h' => lt_asymm h h'
  have h2 : a ≠ b := ne_of_lt h
  simp [lowMat, h1, h2]

theorem mat_nFrame (X : Data E r) (hp : X.p0 = 1) (z : V (nd X)) (τ : X.Ψ) :
    mat (nFrame X z) τ = lowMat (zOf X z τ) := by
  rw [← nmat_eq_lowMat]
  ext a b
  show ∑ c, zFrame X z τ a c * leviFrame X z τ c b = nmat X z τ a b
  simp only [zFrame, leviFrame, hp]
  have hr : 0 < r := lt_of_le_of_lt (Nat.zero_le _) a.isLt
  have n00 : ∀ c : Fin r, nmat X z τ c c = 1 := fun c => by simp [nmat]
  have nup : ∀ c d : Fin r, c < d → nmat X z τ c d = 0 := fun c d h => by
    have h1 : ¬ d < c := fun h' => lt_asymm h h'
    have h2 : c ≠ d := ne_of_lt h
    simp [nmat, h1, h2]
  by_cases hb : (b : ℕ) < 1
  · have hb0 : b = ⟨0, hr⟩ := Fin.ext (by simp; omega)
    subst hb0
    rw [Finset.sum_eq_single ⟨0, hr⟩]
    · by_cases ha : 1 ≤ (a : ℕ)
      · simp [ha, n00]
      · have ha0 : a = ⟨0, hr⟩ := Fin.ext (by simp; omega)
        subst ha0; simp [n00]
    · intro c _ hc
      have hc1 : 1 ≤ (c : ℕ) := by
        by_contra h; apply hc; exact Fin.ext (by simp; omega)
      simp [hc1]
    · simp
  · rw [Finset.sum_eq_single a]
    · have : ¬ (1 ≤ (a : ℕ) ∧ (a : ℕ) < 1) := by omega
      simp [this, hb]
      intro h1 h2; omega
    · intro c _ hca
      by_cases hc : (c : ℕ) < 1
      · have h1 : c < b := Fin.lt_def.2 (by omega)
        simp [hb, nup c b h1]
      · have : ¬ (1 ≤ (a : ℕ) ∧ (c : ℕ) < 1) := by omega
        simp [this, Ne.symm hca]
        intro _ _ h3; omega
    · simp

end GlobalTheory.IntBallMinorOne

namespace GlobalTheory.IntBallMinorOne
open Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem gram_eq_transpose (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

theorem gram_mul_right (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (M N : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G (M * N) = Nᵀ * gram τ G M * N.map (starRingEnd ℂ) := by
  rw [gram_eq_transpose, gram_eq_transpose, Matrix.transpose_mul, Matrix.map_mul]
  simp only [Matrix.mul_assoc]

def eR (r : ℕ) (hr : 1 ≤ r) : Fin 1 ⊕ Fin (r - 1) ≃ Fin r :=
  finSumFinEquiv.trans (finCongr (by omega))

def eC (k : ℕ) : Fin 1 ⊕ Fin k ≃ Fin (k + 1) :=
  finSumFinEquiv.trans (finCongr (by omega))

@[simp] theorem eR_inl (hr : 1 ≤ r) (i : Fin 1) : ((eR r hr (Sum.inl i) : Fin r) : ℕ) = i := by
  simp [eR]

@[simp] theorem eR_inr (hr : 1 ≤ r) (i : Fin (r - 1)) : ((eR r hr (Sum.inr i) : Fin r) : ℕ) = 1 + i := by
  simp [eR]

@[simp] theorem eC_inl (k : ℕ) (i : Fin 1) : ((eC k (Sum.inl i) : Fin (k + 1)) : ℕ) = i := by
  simp [eC]

@[simp] theorem eC_inr (k : ℕ) (i : Fin k) : ((eC k (Sum.inr i) : Fin (k + 1)) : ℕ) = 1 + i := by
  simp [eC]; omega

end GlobalTheory.IntBallMinorOne

namespace GlobalTheory.IntBallMinorOne

theorem zDet_mul_colGram_le_norm_dmin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), X.p0 = 1 →
    ∀ (x0 : Base X) (z : V (nd X)), z ∈ Om X → ∀ (τ : X.Ψ) (k : Fin (r - 1)),
    zDet X z τ * colGram (blkW X.p0 (zOf X z τ)) k.castSucc ≤
      ‖dmin X.Gm (point X x0 z) τ ⟨(k : ℕ) + 1, by omega⟩‖ := by
  intro E _ _ _ r X hp x0 z hz τ k
  have hr : 1 ≤ r := by have := k.isLt; omega
  have hk : (k : ℕ) + 1 ≤ r := by have := k.isLt; omega
  set w := zOf X z τ with hw
  set L : Matrix (Fin r) (Fin r) ℂ := lowMat w with hL
  set D : Matrix (Fin r) (Fin r) ℂ := Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) with hD
  have hgram : gram τ.1 X.Gm (mat (point X x0 z) τ) = Lᵀ * D * L.map (starRingEnd ℂ) := by
    have : mat (point X x0 z) τ = mat x0.1 τ * mat (nFrame X z) τ := rfl
    rw [this, gram_mul_right, x0.2 τ, mat_nFrame X hp]
  set f : Fin 1 ⊕ Fin k → Fin r := fun j => Fin.castLE hk (eC k j) with hf
  set A : Matrix (Fin 1 ⊕ Fin (r - 1)) (Fin 1 ⊕ Fin k) ℂ := L.submatrix (eR r hr) f with hA
  set D' : Matrix (Fin 1 ⊕ Fin (r - 1)) (Fin 1 ⊕ Fin (r - 1)) ℂ := D.submatrix (eR r hr) (eR r hr) with hD'
  have hdmin : dmin X.Gm (point X x0 z) τ ⟨(k : ℕ) + 1, by omega⟩ = (Aᵀ * D' * A.map (starRingEnd ℂ)).det := by
    unfold dmin lminor
    rw [hgram, ← Matrix.det_submatrix_equiv_self (eC k), Matrix.submatrix_submatrix]
    congr 1
    rw [Matrix.submatrix_mul _ _ _ (eR r hr) _ (eR r hr).bijective,
      Matrix.submatrix_mul _ _ _ (eR r hr) _ (eR r hr).bijective, hA, hD', Matrix.transpose_submatrix,
      Matrix.submatrix_map]
    rfl
  set Zm : Matrix (Fin (r - 1)) (Fin 1) ℂ := fun i _ => A (Sum.inr i) (Sum.inl 0) with hZm
  set Nm : Matrix (Fin (r - 1)) (Fin k) ℂ := fun i j => A (Sum.inr i) (Sum.inr j) with hNm
  have hAb : A = Matrix.fromBlocks 1 0 Zm Nm := by
    ext (i | i) (j | j)
    · have h : eR r hr (Sum.inl i) = f (Sum.inl j) := Fin.ext (by simp [hf, Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j])
      simp only [Matrix.fromBlocks_apply₁₁, hA, Matrix.submatrix_apply]
      rw [h, hL, lowMat_diag, Subsingleton.elim i j, Matrix.one_apply_eq]
    · have h : eR r hr (Sum.inl i) < f (Sum.inr j) := Fin.lt_def.2 (by simp [hf, Fin.fin_one_eq_zero i])
      simp only [Matrix.fromBlocks_apply₁₂, hA, Matrix.submatrix_apply, Matrix.zero_apply]
      rw [hL, lowMat_upper w h]
    · rw [Fin.fin_one_eq_zero j]; rfl
    · rfl
  have hDb : D' = Matrix.fromBlocks 1 0 0 (-1) := by
    ext (i | i) (j | j) <;>
      simp [hD', hD, Matrix.diagonal_apply, sgn, hp, Matrix.one_apply, (eR r hr).injective.eq_iff] <;>
      split_ifs <;> simp
  have hT : Aᵀ * D' * A.map (starRingEnd ℂ) = (Aᴴ * D' * A)ᵀ := by
    have h1 : D'ᵀ = D' := by rw [hDb, Matrix.fromBlocks_transpose]; simp
    have h2 : (Aᴴ)ᵀ = A.map (starRingEnd ℂ) := by ext i j; simp
    rw [Matrix.transpose_mul, Matrix.transpose_mul, h1, h2, Matrix.mul_assoc]
  have hzD : zDet X z τ = (1 - Zmᴴ * Zm).det.re := by
    unfold zDet
    haveI : Unique {b : Fin r // (b : ℕ) < X.p0} :=
      { default := ⟨⟨0, by omega⟩, by show 0 < X.p0; omega⟩
        uniq := fun b => Subtype.ext (Fin.ext (by
          have h1 : ((b : Fin r) : ℕ) < X.p0 := b.2
          show ((b : Fin r) : ℕ) = 0
          omega)) }
    rw [Matrix.det_unique, Matrix.det_fin_one]
    simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.mul_apply, Matrix.conjTranspose_apply]
    have hmem : ∀ i : Fin (r - 1), X.p0 ≤ (i : ℕ) + 1 := fun i => by omega
    let eqv : Fin (r - 1) ≃ {a : Fin r // X.p0 ≤ (a : ℕ)} :=
      { toFun := fun i => ⟨⟨(i : ℕ) + 1, by omega⟩, hmem i⟩
        invFun := fun a => ⟨(a.1 : ℕ) - 1, by have := a.1.2; omega⟩
        left_inv := fun i => Fin.ext (by simp)
        right_inv := fun a => Subtype.ext (Fin.ext (by
          have h1 : X.p0 ≤ ((a : Fin r) : ℕ) := a.2
          show ((a : Fin r) : ℕ) - 1 + 1 = (a : Fin r)
          omega)) }
    have key : ∀ i : Fin (r - 1), Zm i 0 = zBlock X z τ ⟨⟨(i : ℕ) + 1, by omega⟩, hmem i⟩ default := by
      intro i
      simp only [hZm, hA, Matrix.submatrix_apply, hL, zBlock, Matrix.of_apply]
      rw [← congrFun (congrFun (nmat_eq_lowMat X z τ) _) _, Matrix.of_apply]
      congr 1
      · exact Fin.ext (by simp; omega)
      · have h1 : (((default : {b : Fin r // (b : ℕ) < X.p0}) : Fin r) : ℕ) < X.p0 :=
          (default : {b : Fin r // (b : ℕ) < X.p0}).2
        exact Fin.ext (by simp [hf]; omega)
    congr 2
    exact (Fintype.sum_equiv eqv _ _ fun i => by rw [key i]; rfl).symm
  have hcG : colGram (blkW X.p0 (zOf X z τ)) k.castSucc = ‖(Nmᴴ * Nm).det‖ := by
    unfold colGram lminor
    rw [Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, ← Matrix.conjTranspose_submatrix]
    have hN : (blkW X.p0 (zOf X z τ)).submatrix id (Fin.castLE (Nat.le_of_lt_succ (Fin.castSucc k).isLt)) = Nm := by
      ext i j
      simp only [Matrix.submatrix_apply, blkW, hp, if_true, hNm, hA, hL, id]
      congr 1
      · exact Fin.ext (by simp; omega)
      · exact Fin.ext (by simp [hf]; omega)
    rw [hN]
  rw [hdmin, hT, Matrix.det_transpose, hzD, hcG, hAb, hDb]
  apply schur_bound
  rw [← hzD]
  exact zDet_pos X hz τ

end GlobalTheory.IntBallMinorOne
