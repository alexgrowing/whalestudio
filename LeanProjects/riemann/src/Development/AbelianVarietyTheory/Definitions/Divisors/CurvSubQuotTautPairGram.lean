import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm

open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.HermFrame.Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {m l : Type*} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]
  {H : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E}

theorem blockSS_eq (K T : Matrix (m ⊕ l) (m ⊕ l) ℂ) :
    blockSS K T = T.toBlocks₁₁ + orthCoeff K * T.toBlocks₂₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks T]
  simp [blockSS, orthProj, incl, fromCols_mul_fromBlocks, fromCols_mul_fromRows]

theorem blockQQ_eq (K T : Matrix (m ⊕ l) (m ⊕ l) ℂ) :
    blockQQ K T = T.toBlocks₂₂ - T.toBlocks₂₁ * orthCoeff K := by
  conv_lhs => rw [← fromBlocks_toBlocks T]
  simp [blockQQ, quotMap, orthLift, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
  abel

theorem conn_sub (hu : IsUnit (H z).det) (hs : IsUnit (subGram (H z)).det) (ξ : E) :
    conn (fun x => subGram (H x)) z ξ = blockSS (H z) (conn H z ξ) := by
  have h := transpose_mul_conn hu ξ
  rw [← fromBlocks_toBlocks (H z)ᵀ, ← fromBlocks_toBlocks (conn H z ξ), fromBlocks_multiply] at h
  have h1 := congrArg toBlocks₁₁ h
  rw [toBlocks_fromBlocks₁₁] at h1
  have hs' : IsUnit (H z).toBlocks₁₁ᵀ.det := by rwa [det_transpose]
  rw [blockSS_eq, conn,
    show (mdel (fun x => subGram (H x)) z ξ)ᵀ = (mdel H z ξ)ᵀ.toBlocks₁₁ from rfl, ← h1,
    show (H z)ᵀ.toBlocks₁₁ = (H z).toBlocks₁₁ᵀ from rfl,
    show (H z)ᵀ.toBlocks₁₂ = (H z).toBlocks₂₁ᵀ from rfl, subGram, Matrix.mul_add,
    nonsing_inv_mul_cancel_left _ _ hs', orthCoeff, Matrix.mul_assoc]

omit [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] [Fintype l] [DecidableEq l] in

theorem mContDiffAt_orthCoeff {k : WithTop ℕ∞} (h : MContDiffAt k H z)
    (hs : IsUnit (subGram (H z)).det) : MContDiffAt k (fun x => orthCoeff (H x)) z :=
  (h.subGram.transpose.inv (by rwa [det_transpose])).mul (h.submatrix Sum.inr Sum.inl).transpose

theorem mdbar_orthCoeff (h : MContDiffAt 1 H z) (hh : ∀ᶠ x in 𝓝 z, (H x).IsHermitian)
    (hu : IsUnit (H z).det) (hs : IsUnit (subGram (H z)).det) (η : E) :
    mdbar (fun x => orthCoeff (H x)) z η = secondFormAdj H z η := by
  have := extForm_eq_neg_secondFormAdj h hh hu hs η
  rwa [extForm_eq_neg_mdbar, neg_inj] at this

theorem curv_sub (h : MContDiffAt 2 H z) (hh : ∀ᶠ x in 𝓝 z, (H x).IsHermitian)
    (hu : IsUnit (H z).det) (hs : IsUnit (subGram (H z)).det) (ξ η : E) :
    curv (fun x => subGram (H x)) z ξ η =
      blockSS (H z) (curv H z ξ η) - secondFormAdj H z η * secondForm H z ξ := by
  have h1 : MContDiffAt 1 H z := h.of_le one_le_two
  have hc : MContDiffAt 1 (fun x => conn H x ξ) z := h.conn hu (by norm_num) ξ
  have he : (fun x => conn (fun x => subGram (H x)) x ξ) =ᶠ[𝓝 z]
      fun x => (conn H x ξ).toBlocks₁₁ + orthCoeff (H x) * (conn H x ξ).toBlocks₂₁ := by
    filter_upwards [h.eventually_isUnit hu, h.subGram.eventually_isUnit hs] with x a b
    rw [conn_sub (H := H) a b, blockSS_eq]
  have c11 : MContDiffAt 1 (fun x => (conn H x ξ).toBlocks₁₁) z := hc.submatrix Sum.inl Sum.inl
  have c21 : MContDiffAt 1 (fun x => (conn H x ξ).toBlocks₂₁) z := hc.submatrix Sum.inr Sum.inl
  have ho := mContDiffAt_orthCoeff h1 hs
  rw [curv, mdbar_congr he, mdbar_add c11 (ho.mul c21), mdbar_mul ho c21,
    mdbar_orthCoeff h1 hh hu hs, blockSS_eq, secondForm_eq,
    show (curv H z ξ η).toBlocks₁₁ = -mdbar (fun x => (conn H x ξ).toBlocks₁₁) z η from rfl,
    show (curv H z ξ η).toBlocks₂₁ = -mdbar (fun x => (conn H x ξ).toBlocks₂₁) z η from rfl,
    Matrix.mul_neg]
  abel

theorem conn_quot (h : MContDiffAt 1 H z) (hu : IsUnit (H z).det)
    (hs : IsUnit (subGram (H z)).det) (ξ : E) :
    conn (fun x => quotGram (H x)) z ξ = blockQQ (H z) (conn H z ξ) := by
  refine (eq_conn_of_compatible (H := fun x => quotGram (H x))
    (isUnit_det_quotGram hu hs) ?_).symm
  have hA : MContDiffAt 1 (fun x => (H x).toBlocks₁₁) z := h.subGram
  have hB : MContDiffAt 1 (fun x => (H x).toBlocks₁₂) z := h.submatrix Sum.inl Sum.inr
  have hC : MContDiffAt 1 (fun x => (H x).toBlocks₂₁) z := h.submatrix Sum.inr Sum.inl
  have hD : MContDiffAt 1 (fun x => (H x).toBlocks₂₂) z := h.submatrix Sum.inr Sum.inr
  have hs' : IsUnit (H z).toBlocks₁₁.det := hs
  have e := conn_transpose_mul hu ξ
  rw [← fromBlocks_toBlocks (conn H z ξ)ᵀ, ← fromBlocks_toBlocks (H z), fromBlocks_multiply] at e
  have e11 := congrArg toBlocks₁₁ e
  have e12 := congrArg toBlocks₁₂ e
  have e21 := congrArg toBlocks₂₁ e
  have e22 := congrArg toBlocks₂₂ e
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂] at e11 e12 e21 e22
  simp only [quotGram, sub_eq_add_neg]
  rw [mdel_add hD ((hC.mul (hA.inv hs')).mul hB).neg, mdel_neg, mdel_mul (hC.mul (hA.inv hs')) hB,
    mdel_mul hC (hA.inv hs'), mdel_inv hA hs',
    show mdel (fun x => (H x).toBlocks₁₁) z ξ = (mdel H z ξ).toBlocks₁₁ from rfl,
    show mdel (fun x => (H x).toBlocks₁₂) z ξ = (mdel H z ξ).toBlocks₁₂ from rfl,
    show mdel (fun x => (H x).toBlocks₂₁) z ξ = (mdel H z ξ).toBlocks₂₁ from rfl,
    show mdel (fun x => (H x).toBlocks₂₂) z ξ = (mdel H z ξ).toBlocks₂₂ from rfl,
    ← e11, ← e12, ← e21, ← e22, blockQQ_eq, transpose_sub, transpose_mul, orthCoeff, transpose_mul,
    transpose_transpose, transpose_nonsing_inv, transpose_transpose,
    show (conn H z ξ).toBlocks₂₂ᵀ = (conn H z ξ)ᵀ.toBlocks₂₂ from rfl,
    show (conn H z ξ).toBlocks₂₁ᵀ = (conn H z ξ)ᵀ.toBlocks₁₂ from rfl]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_neg, Matrix.neg_mul,
    Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hs']
  abel

theorem curv_quot (h : MContDiffAt 2 H z) (hh : ∀ᶠ x in 𝓝 z, (H x).IsHermitian)
    (hu : IsUnit (H z).det) (hs : IsUnit (subGram (H z)).det) (ξ η : E) :
    curv (fun x => quotGram (H x)) z ξ η =
      blockQQ (H z) (curv H z ξ η) + secondForm H z ξ * secondFormAdj H z η := by
  have h1 : MContDiffAt 1 H z := h.of_le one_le_two
  have hc : MContDiffAt 1 (fun x => conn H x ξ) z := h.conn hu (by norm_num) ξ
  have he : (fun x => conn (fun x => quotGram (H x)) x ξ) =ᶠ[𝓝 z]
      fun x => (conn H x ξ).toBlocks₂₂ + -((conn H x ξ).toBlocks₂₁ * orthCoeff (H x)) := by
    filter_upwards [h.eventually_two, h.eventually_isUnit hu, h.subGram.eventually_isUnit hs]
      with x c a b
    rw [conn_quot (c.of_le one_le_two) a b, blockQQ_eq, sub_eq_add_neg]
  have c22 : MContDiffAt 1 (fun x => (conn H x ξ).toBlocks₂₂) z := hc.submatrix Sum.inr Sum.inr
  have c21 : MContDiffAt 1 (fun x => (conn H x ξ).toBlocks₂₁) z := hc.submatrix Sum.inr Sum.inl
  have ho := mContDiffAt_orthCoeff h1 hs
  rw [curv, mdbar_congr he, mdbar_add c22 (c21.mul ho).neg, mdbar_neg, mdbar_mul c21 ho,
    mdbar_orthCoeff h1 hh hu hs, blockQQ_eq, secondForm_eq,
    show (curv H z ξ η).toBlocks₂₂ = -mdbar (fun x => (conn H x ξ).toBlocks₂₂) z η from rfl,
    show (curv H z ξ η).toBlocks₂₁ = -mdbar (fun x => (conn H x ξ).toBlocks₂₁) z η from rfl,
    Matrix.neg_mul]
  abel

def pairFrame (z : ℂ) : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ :=
  fromBlocks 1 0 (of fun _ _ => z) 1

theorem tautPairGram_eq (z : ℂ) :
    tautPairGram z = (pairFrame z)ᵀ * (fun _ : ℂ => 1) z * (pairFrame z)ᴴᵀ := by
  ext (a | a) (b | b) <;> simp [tautPairGram, pairFrame, mul_apply]

theorem mContDiffAt_pairFrame (k : WithTop ℕ∞) (z : ℂ) : MContDiffAt k pairFrame z := by
  rintro (a | a) (b | b) <;> simp only [pairFrame, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
    fromBlocks_apply₂₁, fromBlocks_apply₂₂, of_apply] <;> fun_prop

theorem det_pairFrame (z : ℂ) : (pairFrame z).det = 1 := by
  simp [pairFrame, det_fromBlocks_zero₁₂]

theorem isPosFrame_tautPairGram : IsPosFrame Set.univ tautPairGram := by
  refine ⟨isOpen_univ, fun a b z _ => ?_, fun z _ => ?_⟩
  · simp only [funext tautPairGram_eq]
    exact ((((mContDiffAt_pairFrame ∞ z).transpose.mul (mContDiffAt_const 1)).mul
      (mContDiffAt_pairFrame ∞ z).conjTranspose.transpose) a b).contDiffWithinAt
  · rw [tautPairGram_eq, ← PosDef.transpose_iff]
    simp only [transpose_mul, transpose_transpose, Matrix.mul_one]
    exact PosDef.conjTranspose_mul_self _ (mulVec_injective_iff_isUnit.2
      ((isUnit_iff_isUnit_det _).2 (by simp [det_pairFrame])))

theorem curv_tautPairGram (z ξ η : ℂ) : curv tautPairGram z ξ η = 0 := by
  rw [funext tautPairGram_eq, curv_changeFrame (mContDiffAt_const 1) (by simp)
    (mContDiffAt_pairFrame 2 z) (by simp [det_pairFrame])
    (Eventually.of_forall fun x η => ?_)]
  · simp
  · ext (a | a) (b | b) <;> simp only [mdbar_apply, pairFrame, fromBlocks_apply₁₁,
      fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, of_apply] <;>
      rw [dbar_eq_zero (by fun_prop)] <;> rfl

theorem secondForm_tautPairGram (ξ : ℂ) : secondForm tautPairGram 0 ξ = of fun _ _ => ξ := by
  have h : tautPairGram 0 = 1 := by
    rw [← fromBlocks_one]; ext (a | a) (b | b) <;> simp [tautPairGram]
  ext a b
  rw [secondForm_eq, conn, h, transpose_one, inv_one, Matrix.one_mul]
  change del (fun x : ℂ => x) 0 ξ = ξ
  rw [del_eq_fderiv differentiableAt_fun_id]; simp

theorem secondFormAdj_tautPairGram (η : ℂ) :
    secondFormAdj tautPairGram 0 η = of fun _ _ => conj η := by
  have h : tautPairGram 0 = 1 := by
    rw [← fromBlocks_one]; ext (a | a) (b | b) <;> simp [tautPairGram]
  have h1 : subGram (1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ) = 1 := by
    rw [← fromBlocks_one]; rfl
  have h2 : quotGram (1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ) = 1 := by
    have : toBlocks₂₁ (1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ) = 0 := by
      rw [← fromBlocks_one]; rfl
    rw [quotGram, this, Matrix.zero_mul, Matrix.zero_mul, sub_zero, ← fromBlocks_one]; rfl
  rw [secondFormAdj, h, h1, h2, secondForm_tautPairGram]
  ext a b; simp [adj]

theorem curv_sub_quot_tautPairGram (ξ η : ℂ) :
    curv (fun x => subGram (tautPairGram x)) 0 ξ η () () = -(ξ * conj η) ∧
    curv (fun x => quotGram (tautPairGram x)) 0 ξ η () () = ξ * conj η ∧
    extTrace tautPairGram 0 ξ η = kappa * (ξ * conj η) := by
  have h := isPosFrame_tautPairGram.isHermFrame
  have hs := isPosFrame_tautPairGram.sub.isHermFrame.isUnit 0 trivial
  have a := h.two (z := 0) trivial
  have b := h.eventually_herm (z := 0) trivial
  have c := h.isUnit 0 trivial
  rw [curv_sub a b c hs, curv_quot a b c hs, extTrace,
    extFormAdj_eq_neg_secondForm (h.one trivial) b c hs,
    extForm_eq_neg_secondFormAdj (h.one trivial) b c hs, curv_tautPairGram,
    secondForm_tautPairGram, secondFormAdj_tautPairGram]
  simp [blockSS, blockQQ, mul_apply, trace, mul_comm]

example : wedge (fun ξ η : Fin 2 → ℂ => ξ 0 * conj (η 0)) (fun ξ η => ξ 1 * conj (η 1))
      ![1, 0] ![1, 0] ![0, 1] ![0, 1] = 1 ∧
    wedge (fun ξ η : Fin 2 → ℂ => ξ 0 * conj (η 0)) (fun ξ η => ξ 1 * conj (η 1))
      ![1, 0] ![0, 1] ![0, 1] ![1, 0] = -1 := by
  simp [wedge]

example (C : ℝ) : ¬ OneFormBound {0} (fun _ : Fin 1 → ℂ => (0 : Matrix (Fin 1) (Fin 1) ℂ))
    (fun _ => 1) (fun _ _ => 1) C := fun h => by
  simpa using (h 0 rfl).1.diag_pos (i := 0)

end GlobalTheory.HermFrame.Model
