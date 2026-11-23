import Mathlib
import Formalism.DegreeFormula.Statement

noncomputable section

open Matrix Formalism.DegreeFormula Formalism.MJ Formalism.UG
open scoped ComplexOrder

namespace GlobalTheory.HodgeDomain

variable {p q : ℕ}

def jW (g : GL (Fin p ⊕ Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₁ -
    moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z * (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₂₁

theorem upq_iff {g : GL (Fin p ⊕ Fin q) ℂ} : g ∈ Upq p q ↔
    (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ * Jpq p q * g = Jpq p q := by
  unfold Upq UJ
  simp only [Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq]
  have hc : cT (starRingEnd ℂ) (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ := by
    ext i j
    simp [cT, conjTranspose_apply]
  rw [hc]

theorem Jpq_sq : Jpq p q * Jpq p q = 1 := by
  unfold Jpq
  rw [fromBlocks_multiply]
  simp

theorem upq_right {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) :
    (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * Jpq p q * (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ =
      Jpq p q := by
  have h := upq_iff.mp hg
  generalize (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = G at h ⊢
  have h1 : (Jpq p q * Gᴴ * Jpq p q) * G = 1 := by
    rw [show Jpq p q * Gᴴ * Jpq p q * G = Jpq p q * (Gᴴ * Jpq p q * G) by simp only [Matrix.mul_assoc], h, Jpq_sq]
  have h2 : G * (Jpq p q * Gᴴ * Jpq p q) = 1 := by
    rw [← Matrix.inv_eq_left_inv h1]
    exact Matrix.mul_nonsing_inv _ (Matrix.isUnit_det_of_left_inverse h1)
  calc G * Jpq p q * Gᴴ = G * (Jpq p q * Gᴴ * Jpq p q) * Jpq p q := by
        simp only [Matrix.mul_assoc, Jpq_sq, Matrix.mul_one]
    _ = Jpq p q := by rw [h2, Matrix.one_mul]

private lemma Jpq_mul_fromRows {n : Type*} (C : Matrix (Fin p) n ℂ) (D : Matrix (Fin q) n ℂ) :
    Jpq p q * fromRows C D = fromRows C (-D) := by
  ext (i | i) j <;> simp [Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

private lemma conjTranspose_fromRows_mul_Jpq_mul_fromRows {n m : Type*} (A : Matrix (Fin p) n ℂ) (B : Matrix (Fin q) n ℂ)
    (C : Matrix (Fin p) m ℂ) (D : Matrix (Fin q) m ℂ) :
    (fromRows A B)ᴴ * Jpq p q * fromRows C D = Aᴴ * C - Bᴴ * D := by
  rw [Matrix.mul_assoc, Jpq_mul_fromRows]
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_sum_type, sub_eq_add_neg]

private lemma fromCols_mul_Jpq {m : Type*} (A : Matrix m (Fin p) ℂ) (B : Matrix m (Fin q) ℂ) :
    fromCols A B * Jpq p q = fromCols A (-B) := by
  ext i (j | j) <;> simp [Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

private lemma fromCols_mul_Jpq_mul_conjTranspose_fromCols {m n : Type*} (A : Matrix m (Fin p) ℂ) (B : Matrix m (Fin q) ℂ)
    (C : Matrix n (Fin p) ℂ) (D : Matrix n (Fin q) ℂ) :
    fromCols A B * Jpq p q * (fromCols C D)ᴴ = A * Cᴴ - B * Dᴴ := by
  rw [fromCols_mul_Jpq]
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_sum_type, sub_eq_add_neg]

private lemma blocks_mul_fromRows {n : Type*} (M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
    (X : Matrix (Fin p) n ℂ) (Y : Matrix (Fin q) n ℂ) :
    M * fromRows X Y = fromRows (M.toBlocks₁₁ * X + M.toBlocks₁₂ * Y) (M.toBlocks₂₁ * X + M.toBlocks₂₂ * Y) := by
  ext (i | i) j <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
    Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]

theorem kapQ_gram {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) (z : Matrix (Fin p) (Fin q) ℂ) :
    (kapQ g z)ᴴ * kapQ g z -
      ((g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₁ * z +
        (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₂)ᴴ *
      ((g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₁ * z +
        (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₂) = hQ z := by
  have h := upq_iff.mp hg
  unfold kapQ hQ
  generalize (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = G at h ⊢
  have e1 : (G * fromRows z (1 : Matrix (Fin q) (Fin q) ℂ))ᴴ * Jpq p q * (G * fromRows z (1 : Matrix (Fin q) (Fin q) ℂ)) =
      (fromRows z (1 : Matrix (Fin q) (Fin q) ℂ))ᴴ * Jpq p q * fromRows z (1 : Matrix (Fin q) (Fin q) ℂ) := by
    rw [conjTranspose_mul]
    conv_rhs => rw [← h]
    simp only [Matrix.mul_assoc]
  rw [blocks_mul_fromRows, conjTranspose_fromRows_mul_Jpq_mul_fromRows, conjTranspose_fromRows_mul_Jpq_mul_fromRows] at e1
  simp only [Matrix.mul_one, conjTranspose_one] at e1
  simpa only [neg_sub] using congrArg Neg.neg e1

theorem kapQ_isUnit {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) {z : Matrix (Fin p) (Fin q) ℂ}
    (hz : z ∈ hcDom p q) : IsUnit (kapQ g z).det := by
  have h1 := kapQ_gram hg z
  have hpd : ((kapQ g z)ᴴ * kapQ g z).PosDef := by
    rw [eq_add_of_sub_eq h1]
    exact Matrix.PosDef.add_posSemidef (by exact hz) (posSemidef_conjTranspose_mul_self _)
  rw [isUnit_iff_ne_zero]
  intro h0
  have := hpd.det_pos
  rw [det_mul, det_conjTranspose, h0, mul_zero] at this
  exact lt_irrefl _ this

theorem moeb_mul_kapQ {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) {z : Matrix (Fin p) (Fin q) ℂ}
    (hz : z ∈ hcDom p q) : moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z * kapQ g z =
      (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₁ * z +
        (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₂ := by
  have hu := kapQ_isUnit hg hz
  calc moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z * kapQ g z =
      ((g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₁ * z + (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₂) *
        ((kapQ g z)⁻¹ * kapQ g z) := by
        rw [moeb, Matrix.mul_assoc]; rfl
    _ = _ := by rw [Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

theorem hQ_moeb {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) {z : Matrix (Fin p) (Fin q) ℂ}
    (hz : z ∈ hcDom p q) :
    (kapQ g z)ᴴ * hQ (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z) * kapQ g z = hQ z := by
  have e := moeb_mul_kapQ hg hz
  have h1 := kapQ_gram hg z
  calc (kapQ g z)ᴴ * hQ (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z) * kapQ g z =
      (kapQ g z)ᴴ * kapQ g z - (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z * kapQ g z)ᴴ * (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z * kapQ g z) := by
        unfold hQ
        rw [conjTranspose_mul]
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
    _ = hQ z := by rw [e]; exact h1

theorem moeb_mem {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) {z : Matrix (Fin p) (Fin q) ℂ}
    (hz : z ∈ hcDom p q) : moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z ∈ hcDom p q := by
  have hu : IsUnit (kapQ g z) := (Matrix.isUnit_iff_isUnit_det _).mpr (kapQ_isUnit hg hz)
  have h2 : ((kapQ g z)ᴴ * hQ (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z) * kapQ g z).PosDef := by
    rw [hQ_moeb hg hz]; exact hz
  exact (Matrix.IsUnit.posDef_star_left_conjugate_iff hu).mp h2

private lemma fromCols_mul_eq_blocks {m : Type*} (X : Matrix m (Fin p) ℂ) (Y : Matrix m (Fin q) ℂ)
    (M : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) :
    fromCols X Y * M = fromCols (X * M.toBlocks₁₁ + Y * M.toBlocks₂₁) (X * M.toBlocks₁₂ + Y * M.toBlocks₂₂) := by
  ext i (j | j) <;> simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂,
    Matrix.toBlocks₂₁, Matrix.toBlocks₂₂]

private lemma mul_fromCols' {m k : Type*} [Fintype m] (N : Matrix k m ℂ) (X : Matrix m (Fin p) ℂ)
    (Y : Matrix m (Fin q) ℂ) : N * fromCols X Y = fromCols (N * X) (N * Y) := by
  ext i (j | j) <;> simp [Matrix.mul_apply]

theorem hP_moeb {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) {z : Matrix (Fin p) (Fin q) ℂ}
    (hz : z ∈ hcDom p q) :
    jW g z * hP z * (jW g z)ᴴ = hP (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z) := by
  have h := upq_right hg
  have e := moeb_mul_kapQ hg hz
  unfold jW hP
  unfold kapQ at e
  generalize (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = G at h e ⊢
  generalize moeb G z = w at e ⊢
  rw [Matrix.mul_add, ← Matrix.mul_assoc] at e
  have k1 : fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-w) * G =
      (G.toBlocks₁₁ - w * G.toBlocks₂₁) * fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-z) := by
    rw [fromCols_mul_eq_blocks, mul_fromCols']
    have b1 : (1 : Matrix (Fin p) (Fin p) ℂ) * G.toBlocks₁₁ + -w * G.toBlocks₂₁ = (G.toBlocks₁₁ - w * G.toBlocks₂₁) * 1 := by
      rw [Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul, sub_eq_add_neg]
    have b2 : (1 : Matrix (Fin p) (Fin p) ℂ) * G.toBlocks₁₂ + -w * G.toBlocks₂₂ = (G.toBlocks₁₁ - w * G.toBlocks₂₁) * -z := by
      rw [Matrix.one_mul, Matrix.neg_mul, eq_sub_of_add_eq' e, Matrix.mul_neg, Matrix.sub_mul]
      abel
    rw [b1, b2]
  have k2 : (G.toBlocks₁₁ - w * G.toBlocks₂₁) *
        (fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-z) * Jpq p q * (fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-z))ᴴ) *
        (G.toBlocks₁₁ - w * G.toBlocks₂₁)ᴴ =
      fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-w) * Jpq p q * (fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-w))ᴴ := by
    calc _ = ((G.toBlocks₁₁ - w * G.toBlocks₂₁) * fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-z)) * Jpq p q *
          ((G.toBlocks₁₁ - w * G.toBlocks₂₁) * fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-z))ᴴ := by
            rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = (fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-w) * G) * Jpq p q * (fromCols (1 : Matrix (Fin p) (Fin p) ℂ) (-w) * G)ᴴ := by
            rw [k1]
      _ = _ := by
            rw [conjTranspose_mul]
            conv_rhs => rw [← h]
            simp only [Matrix.mul_assoc]
  rw [fromCols_mul_Jpq_mul_conjTranspose_fromCols, fromCols_mul_Jpq_mul_conjTranspose_fromCols] at k2
  simpa only [conjTranspose_one, Matrix.mul_one, conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg] using k2

theorem hP_mul_eq_one {z : Matrix (Fin p) (Fin q) ℂ} (hz : z ∈ hcDom p q) :
    hP z * (1 + z * (hQ z)⁻¹ * zᴴ) = 1 := by
  have hpd : (hQ z).PosDef := hz
  have hu : IsUnit (hQ z).det := isUnit_iff_ne_zero.mpr hpd.det_pos.ne'
  have key : z * (hQ z * (hQ z)⁻¹) * zᴴ = z * zᴴ := by rw [Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  generalize (hQ z)⁻¹ = R at key ⊢
  unfold hQ at key
  unfold hP
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_assoc] at key ⊢
  rw [← key]
  abel

theorem hP_inv_posDef {z : Matrix (Fin p) (Fin q) ℂ} (hz : z ∈ hcDom p q) : (hP z)⁻¹.PosDef := by
  have e : (hP z)⁻¹ = 1 + z * (hQ z)⁻¹ * zᴴ := Matrix.inv_eq_right_inv (hP_mul_eq_one hz)
  rw [e]
  have hq : (hQ z).PosDef := hz
  exact Matrix.PosDef.one.add_posSemidef (hq.inv.posSemidef.mul_mul_conjTranspose_same z)

theorem hP_posDef {z : Matrix (Fin p) (Fin q) ℂ} (hz : z ∈ hcDom p q) : (hP z).PosDef := by
  have hu : IsUnit (hP z).det := Matrix.isUnit_det_of_right_inverse (hP_mul_eq_one hz)
  have h := (hP_inv_posDef hz).inv
  rwa [Matrix.nonsing_inv_nonsing_inv _ hu] at h

theorem jW_isUnit {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) {z : Matrix (Fin p) (Fin q) ℂ}
    (hz : z ∈ hcDom p q) : IsUnit (jW g z).det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have h := (hP_posDef (moeb_mem hg hz)).det_pos
  rw [← hP_moeb hg hz, det_mul, det_mul, det_conjTranspose, h0] at h
  simp at h

theorem hP_inv_moeb {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) {z : Matrix (Fin p) (Fin q) ℂ}
    (hz : z ∈ hcDom p q) :
    (jW g z)ᴴ * (hP (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z))⁻¹ * jW g z = (hP z)⁻¹ := by
  have hu := jW_isUnit hg hz
  have hu' : IsUnit (jW g z)ᴴ.det := by rw [det_conjTranspose]; exact hu.star
  rw [← hP_moeb hg hz, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_nonsing_inv_cancel_left _ _ hu',
    Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

def autE (g : GL (Fin p ⊕ Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ) :
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := fromBlocks (jW g z) 0 0 (kapQ g z)

theorem autE_isUnit {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) {z : Matrix (Fin p) (Fin q) ℂ}
    (hz : z ∈ hcDom p q) : IsUnit (autE g z).det := by
  unfold autE
  rw [det_fromBlocks_zero₁₂]
  exact (jW_isUnit hg hz).mul (kapQ_isUnit hg hz)

theorem mul_frame {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) {z : Matrix (Fin p) (Fin q) ℂ}
    (hz : z ∈ hcDom p q) :
    (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * fromBlocks 1 z 0 1 =
      fromBlocks 1 (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z) 0 1 *
        fromBlocks (jW g z) 0 (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₂₁ (kapQ g z) := by
  have e := moeb_mul_kapQ hg hz
  unfold jW
  conv_lhs => rw [← fromBlocks_toBlocks (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)]
  rw [fromBlocks_multiply, fromBlocks_multiply]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, e, sub_add_cancel]
  rfl

def tanAct (g : GL (Fin p ⊕ Fin q) ℂ) (z ξ : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin p) (Fin q) ℂ :=
  jW g z * ξ * (kapQ g z)⁻¹

def blkMet (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin q) (Fin q) ℂ) :
    Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := fromBlocks A 0 0 B

theorem blkMet_posDef {A : Matrix (Fin p) (Fin p) ℂ} {B : Matrix (Fin q) (Fin q) ℂ} (hA : A.PosDef)
    (hB : B.PosDef) : (blkMet A B).PosDef := by
  unfold blkMet
  have hpsd : (fromBlocks A 0 0 B).PosSemidef := by
    let _ := Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr hA.det_pos.ne')
    have h0 : (0 : Matrix (Fin q) (Fin p) ℂ) = (0 : Matrix (Fin p) (Fin q) ℂ)ᴴ := by simp
    rw [h0]
    exact (Matrix.PosDef.fromBlocks₁₁ _ _ hA).2 (by simpa using hB.posSemidef)
  refine hpsd.posDef_iff_isUnit.2 ?_
  rw [Matrix.isUnit_iff_isUnit_det, det_fromBlocks_zero₁₂]
  exact (isUnit_iff_ne_zero.mpr hA.det_pos.ne').mul (isUnit_iff_ne_zero.mpr hB.det_pos.ne')

theorem autE_blkMet (g : GL (Fin p ⊕ Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ)
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin q) (Fin q) ℂ) :
    (autE g z)ᴴ * blkMet A B * autE g z =
      blkMet ((jW g z)ᴴ * A * jW g z) ((kapQ g z)ᴴ * B * kapQ g z) := by
  unfold autE blkMet
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply]
  simp [Matrix.mul_assoc]

def hodge (c : ℝ) (z : Matrix (Fin p) (Fin q) ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ :=
  blkMet ((c : ℂ) • (hP z)⁻¹) ((c : ℂ) • hQ z)

theorem hodge_posDef {c : ℝ} (hc : 0 < c) {z : Matrix (Fin p) (Fin q) ℂ} (hz : z ∈ hcDom p q) :
    (hodge c z).PosDef := by
  unfold hodge
  have hc' : (0 : ℂ) < (c : ℂ) := Complex.zero_lt_real.mpr hc
  exact blkMet_posDef ((hP_inv_posDef hz).smul hc') ((show (hQ z).PosDef from hz).smul hc')

theorem hodge_moeb (c : ℝ) {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) {z : Matrix (Fin p) (Fin q) ℂ}
    (hz : z ∈ hcDom p q) :
    (autE g z)ᴴ * hodge c (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z) * autE g z = hodge c z := by
  unfold hodge
  rw [autE_blkMet]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  rw [hP_inv_moeb hg hz, hQ_moeb hg hz]

theorem det_hodge (c : ℝ) {z : Matrix (Fin p) (Fin q) ℂ} (hz : z ∈ hcDom p q) :
    (hodge c z).det = (c : ℂ) ^ (p + q) := by
  unfold hodge blkMet
  have hdet : (hP z).det = (hQ z).det := Matrix.det_one_sub_mul_comm z zᴴ
  have hne : (hQ z).det ≠ 0 := (show (hQ z).PosDef from hz).det_pos.ne'
  rw [det_fromBlocks_zero₁₂, det_smul, det_smul, det_nonsing_inv, Fintype.card_fin, Fintype.card_fin, hdet,
    Ring.inverse_eq_inv', pow_add]
  field_simp

example (c : ℝ) : hodge c (0 : Matrix (Fin p) (Fin q) ℂ) = (c : ℂ) • 1 := by
  simp [hodge, blkMet, hP, hQ, ← fromBlocks_one, fromBlocks_smul]

end GlobalTheory.HodgeDomain
