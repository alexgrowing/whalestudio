import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMTA

noncomputable section

open Matrix
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutEXMT

open Formalism.FourierDecayAlt

section cd

variable {m : ℕ}

theorem cd_det : ContDiff ℝ ∞ (fun M : Fin m → Fin m → ℂ => (Matrix.of M).det) := by
  simp only [Matrix.det_apply, Matrix.of_apply]
  refine ContDiff.sum fun σ _ => ?_
  refine ContDiff.const_smul _ ?_
  exact contDiff_prod fun i _ => by fun_prop

theorem cd_adj (i j : Fin m) : ContDiff ℝ ∞ (fun M : Fin m → Fin m → ℂ => (Matrix.of M).adjugate i j) := by
  have h : (fun M : Fin m → Fin m → ℂ => (Matrix.of M).adjugate i j) =
      (fun N : Fin m → Fin m → ℂ => (Matrix.of N).det) ∘
        (fun M : Fin m → Fin m → ℂ => fun a b => (Matrix.of M).updateRow j (Pi.single i 1) a b) := by
    funext M
    rw [Matrix.adjugate_apply]
    rfl
  rw [h]
  refine cd_det.comp ?_
  refine contDiff_pi.2 fun a => contDiff_pi.2 fun b => ?_
  simp only [Matrix.updateRow_apply, Matrix.of_apply]
  split_ifs <;> fun_prop

theorem cd_inv (i j : Fin m) :
    ContDiffOn ℝ ∞ (fun M : Fin m → Fin m → ℂ => (Matrix.of M)⁻¹ i j) {M | (Matrix.of M).det ≠ 0} := by
  have h1 : ContDiffOn ℝ ∞
      (fun M : Fin m → Fin m → ℂ => ((Matrix.of M).det)⁻¹ * (Matrix.of M).adjugate i j)
      {M | (Matrix.of M).det ≠ 0} :=
    (cd_det.contDiffOn.inv fun M hM => hM).mul (cd_adj i j).contDiffOn
  refine h1.congr fun M _ => ?_
  simp only [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]

end cd

section wm

variable {n : ℕ}

theorem cd_gram (a b : Fin n) : ContDiff ℝ ∞ (fun Z : Fin n → Fin n → ℂ => gram (Matrix.of Z) a b) := by
  simp only [gram, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
  refine ContDiff.sum fun k _ => ContDiff.mul ?_ (by fun_prop)
  exact Complex.conjCLE.contDiff.comp
    (by fun_prop : ContDiff ℝ ∞ fun Z : Fin n → Fin n → ℂ => Z k a)

private lemma det_gram_castLE_ne_zero_of_det_ne_zero (Z : Fin n → Fin n → ℂ) (hZ : (Matrix.of Z).det ≠ 0) (k : ℕ)
    (hk : k ≤ n) :
    (Matrix.of fun a b : Fin k => gram (Matrix.of Z) (Fin.castLE hk a) (Fin.castLE hk b)).det ≠ 0 := by
  set E : Matrix (Fin n) (Fin k) ℂ := (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id (Fin.castLE hk) with hE
  set A : Matrix (Fin n) (Fin k) ℂ := Matrix.of Z * E with hA
  have hA' : ∀ r a, A r a = Z r (Fin.castLE hk a) := by
    intro r a
    simp [hA, hE, Matrix.mul_apply, Matrix.one_apply]
  have hB : (Matrix.of fun a b : Fin k => gram (Matrix.of Z) (Fin.castLE hk a) (Fin.castLE hk b)) =
      Aᴴ * A := by
    ext a b
    simp only [Matrix.of_apply, gram, Matrix.mul_apply, Matrix.conjTranspose_apply, hA']
  rw [hB]
  intro h0
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have h1 : A *ᵥ v = 0 := by
    open scoped ComplexOrder in
    exact (Matrix.conjTranspose_mul_self_mulVec_eq_zero A v).1 hv
  have h2 : E *ᵥ v = 0 := by
    by_contra hne
    apply hZ
    refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨E *ᵥ v, hne, ?_⟩
    rw [Matrix.mulVec_mulVec, ← hA, h1]
  apply hv0
  funext a
  have := congrFun h2 (Fin.castLE hk a)
  simpa [hE, Matrix.mulVec, dotProduct, Matrix.one_apply, Fin.castLE_inj] using this

theorem cd_Wm (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun Z : Fin n → Fin n → ℂ => Wm (Matrix.of Z) i j) {Z | (Matrix.of Z).det ≠ 0} := by
  simp only [Wm, blkJ, colJ, Matrix.of_apply]
  by_cases hij : (i : ℕ) < j
  · simp only [dif_pos hij, Matrix.mulVec, dotProduct, Pi.neg_apply]
    have hg : ContDiff ℝ ∞ (fun Z : Fin n → Fin n → ℂ => fun a b : Fin j =>
        gram (Matrix.of Z) (Fin.castLE j.isLt.le a) (Fin.castLE j.isLt.le b)) :=
      contDiff_pi.2 fun a => contDiff_pi.2 fun b => cd_gram _ _
    refine ContDiffOn.neg (ContDiffOn.sum fun c _ => ContDiffOn.mul ?_ (cd_gram _ _).contDiffOn)
    exact (cd_inv (m := j) ⟨i, hij⟩ c).comp hg.contDiffOn fun Z hZ => det_gram_castLE_ne_zero_of_det_ne_zero Z hZ j j.isLt.le
  · simp only [dif_neg hij]
    split_ifs <;> exact contDiffOn_const

theorem cd_Sm (i j : Fin n) :
    ContDiffOn ℝ ∞ (fun Z : Fin n → Fin n → ℂ => Sm (Matrix.of Z) i j) {Z | (Matrix.of Z).det ≠ 0} := by
  have hW : ContDiffOn ℝ ∞ (fun Z : Fin n → Fin n → ℂ => fun a b => Wm (Matrix.of Z) a b)
      {Z | (Matrix.of Z).det ≠ 0} :=
    contDiffOn_pi.2 fun a => contDiffOn_pi.2 fun b => cd_Wm a b
  exact (cd_adj i j).comp_contDiffOn hW

end wm

end Formalism.FourierDecayAlt.P.CutEXMT
