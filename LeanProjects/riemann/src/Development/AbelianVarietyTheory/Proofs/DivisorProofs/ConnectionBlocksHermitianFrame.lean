import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HermitianCurvatureForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovariantSecondFundamentalForm
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

noncomputable section

namespace GlobalTheory.SubQuotConn

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V]
variable {m l : Type*} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]

section Leibniz

variable {p k : Type*} [Fintype k] {M : V → Matrix p k ℂ} {v : V → k → ℂ} {z : V}

omit [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V] in

theorem diff_mulVec (hM : MContDiffAt 1 M z) (hv : ∀ a, DifferentiableAt ℝ (fun x => v x a) z)
    (a : p) : DifferentiableAt ℝ (fun x => (M x *ᵥ v x) a) z := by
  simp only [mulVec, dotProduct]
  exact DifferentiableAt.fun_sum fun b _ => (hM.diff a b).fun_mul (hv b)

theorem del_mulVec (hM : MContDiffAt 1 M z) (hv : ∀ a, DifferentiableAt ℝ (fun x => v x a) z)
    (ξ : V) (a : p) : del (fun x => (M x *ᵥ v x) a) z ξ =
      (M z *ᵥ (fun b => del (fun x => v x b) z ξ) + mdel M z ξ *ᵥ v z) a := by
  simp only [mulVec, dotProduct, Pi.add_apply]
  rw [del_sum fun b _ => (hM.diff a b).fun_mul (hv b), ContinuousLinearMap.sum_apply,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b _ => by rw [del_mul (hM.diff a b) (hv b), mdel_apply]

theorem dbar_mulVec (hM : MContDiffAt 1 M z) (hv : ∀ a, DifferentiableAt ℝ (fun x => v x a) z)
    (η : V) (a : p) : dbar (fun x => (M x *ᵥ v x) a) z η =
      (M z *ᵥ (fun b => dbar (fun x => v x b) z η) + mdbar M z η *ᵥ v z) a := by
  simp only [mulVec, dotProduct, Pi.add_apply]
  rw [dbar_sum fun b _ => (hM.diff a b).fun_mul (hv b), ContinuousLinearMap.sum_apply,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b _ => by rw [dbar_mul (hM.diff a b) (hv b), mdbar_apply]

end Leibniz

section Blocks

variable {H : Matrix (m ⊕ l) (m ⊕ l) ℂ}

theorem incl_transpose_mul_mul (M : Matrix (m ⊕ l) (m ⊕ l) ℂ) :
    (incl m l)ᵀ * M * incl m l = M.toBlocks₁₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks M]
  simp [incl, transpose_fromRows, fromCols_mul_fromBlocks, fromCols_mul_fromRows]

theorem orthProj_transpose_mul (hs : IsUnit (subGram H).det) :
    (orthProj H)ᵀ * subGram H = H * incl m l := by
  conv_rhs => rw [← fromBlocks_toBlocks H]
  rw [orthProj, incl, transpose_fromCols, fromRows_mul, fromBlocks_mul_fromRows]
  congr 1
  · simp [subGram]
  · rw [orthCoeff, transpose_mul, transpose_transpose, transpose_nonsing_inv, transpose_transpose,
      subGram, Matrix.mul_assoc, nonsing_inv_mul H.toBlocks₁₁ hs]
    simp

theorem mul_orthLift_conj (hh : H.IsHermitian) (hs : IsUnit (subGram H).det) :
    H * (orthLift H)ᴴᵀ = fromRows 0 (quotGram H) := by
  have := congrArg conjTranspose (orthLift_transpose_mul hs)
  rw [conjTranspose_mul, hh.eq] at this
  rw [show (orthLift H)ᴴᵀ = (orthLift H)ᵀᴴ from rfl, this]
  ext (a | a) b <;> simp [(isHermitian_quotGram hh).apply]

end Blocks

section Frame

variable {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V}

theorem mdel_orthLift (ξ : V) :
    mdel (fun x => orthLift (H x)) z ξ = fromRows (-mdel (fun x => orthCoeff (H x)) z ξ) 0 := by
  ext (a | a) b <;> simp [orthLift, del_neg]

theorem mdbar_orthLift (η : V) :
    mdbar (fun x => orthLift (H x)) z η = fromRows (-mdbar (fun x => orthCoeff (H x)) z η) 0 := by
  ext (a | a) b <;> simp [orthLift, dbar_neg]

theorem quotMap_mul_mdel_orthLift (ξ : V) :
    quotMap m l * mdel (fun x => orthLift (H x)) z ξ = 0 := by
  rw [mdel_orthLift]; simp [quotMap, fromCols_mul_fromRows]

theorem quotMap_mul_mdbar_orthLift (η : V) :
    quotMap m l * mdbar (fun x => orthLift (H x)) z η = 0 := by
  rw [mdbar_orthLift]; simp [quotMap, fromCols_mul_fromRows]

variable (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U)
include h hs hz

theorem conn_gramS (ξ : V) : conn (gramS H) z ξ = orthProj (H z) * conn H z ξ * incl m l := by
  refine (eq_conn_of_compatible (H := gramS H) (hs z hz) ?_).symm
  have e : mdel (gramS H) z ξ = (mdel H z ξ).toBlocks₁₁ := rfl
  rw [e, ← conn_transpose_mul (h.isUnit z hz), ← incl_transpose_mul_mul, transpose_mul,
    transpose_mul]
  simp only [gramS, Matrix.mul_assoc]
  rw [orthProj_transpose_mul (hs z hz)]

theorem conn_gramQ (ξ : V) :
    conn (gramQ H) z ξ = quotMap m l * conn H z ξ * orthLift (H z) := by
  have hH1 := h.one hz
  have hsz := hs z hz
  have hL : MContDiffAt 1 (fun x => orthLift (H x)) z :=
    GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.mContDiffAt_orthLift hH1 hsz
  refine (eq_conn_of_compatible (H := gramQ H)
    (isUnit_det_quotGram (h.isUnit z hz) hsz) ?_).symm
  have hev : gramQ H =ᶠ[𝓝 z] fun x => (orthLift (H x))ᵀ * H x * (orthLift (H x))ᴴᵀ := by
    filter_upwards [h.isOpen.mem_nhds hz] with x hx
    rw [orthLift_transpose_mul (hs x hx)]
    simp [gramQ, orthLift, fromCols_mul_fromRows, conjTranspose_fromRows_eq_fromCols_conjTranspose,
      transpose_fromCols]
  have hK : (quotMap m l)ᵀ * quotGram (H z) = fromRows 0 (quotGram (H z)) := by
    simp [quotMap, transpose_fromCols, fromRows_mul]
  rw [mdel_congr hev, mdel_mul (hL.transpose.mul hH1) hL.conjTranspose.transpose,
    mdel_mul hL.transpose hH1, mdel_transpose (fun x => (orthLift (H x))ᴴ), mdel_conjTranspose,
    mdel_transpose, orthLift_transpose_mul hsz, ← conn_transpose_mul (h.isUnit z hz),
    mdbar_orthLift, mdel_orthLift]
  simp only [Matrix.add_mul, Matrix.mul_assoc, mul_orthLift_conj (h.herm z hz) hsz, transpose_mul,
    gramQ, hK]
  simp [fromCols_mul_fromRows, conjTranspose_fromRows_eq_fromCols_conjTranspose, transpose_fromCols,
    transpose_fromRows]

theorem orthProj_mul_covDel_orthLift (ξ : V) :
    orthProj (H z) * (mdel (fun x => orthLift (H x)) z ξ + conn H z ξ * orthLift (H z)) = 0 := by
  have hH1 := h.one hz
  have hsz := hs z hz
  have hL : MContDiffAt 1 (fun x => orthLift (H x)) z :=
    GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.mContDiffAt_orthLift hH1 hsz
  have hev : (fun x => (orthLift (H x))ᵀ * H x * incl m l) =ᶠ[𝓝 z] fun _ => 0 := by
    filter_upwards [h.isOpen.mem_nhds hz] with x hx
    rw [orthLift_transpose_mul (hs x hx)]
    simp [incl, fromCols_mul_fromRows]
  have h1 := mdel_congr hev ξ
  rw [mdel_const, mdel_mul (hL.transpose.mul hH1) (mContDiffAt_const _), mdel_const,
    Matrix.mul_zero, zero_add, mdel_mul hL.transpose hH1, mdel_transpose,
    ← conn_transpose_mul (h.isUnit z hz)] at h1
  set X := orthProj (H z) * (mdel (fun x => orthLift (H x)) z ξ + conn H z ξ * orthLift (H z))
  have h2 : Xᵀ * subGram (H z) = 0 := by
    rw [transpose_mul, Matrix.mul_assoc, orthProj_transpose_mul hsz, transpose_add, transpose_mul,
      ← h1]
    simp only [Matrix.add_mul, Matrix.mul_assoc]
    abel
  have h3 : Xᵀ = 0 := by
    rw [← Matrix.mul_nonsing_inv_cancel_right (subGram (H z)) Xᵀ hsz, h2, Matrix.zero_mul]
  rw [← transpose_transpose X, h3, transpose_zero]

end Frame

theorem connBlocks_secondForm {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m]
    [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H)
    (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) :
    ConnBlocks H z (fun η => -secondFormAdj H z η) (secondForm H z) := by
  have hH1 := h.one hz
  have hu := h.isUnit z hz
  have hsz := hs z hz
  have hL : MContDiffAt 1 (fun x => orthLift (H x)) z :=
    GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.mContDiffAt_orthLift hH1 hsz
  have hI : MContDiffAt 1 (fun _ : V => incl m l) z := mContDiffAt_const _
  intro u q hu' hq'
  have e1 : ∀ ξ, covDel H (splitSec H u q) z ξ =
      incl m l *ᵥ (fun a => del (fun x => u x a) z ξ) +
        orthLift (H z) *ᵥ (fun a => del (fun x => q x a) z ξ) +
        mdel (fun x => orthLift (H x)) z ξ *ᵥ q z +
        conn H z ξ *ᵥ (incl m l *ᵥ u z + orthLift (H z) *ᵥ q z) := by
    intro ξ
    rw [covDel]
    congr 1
    funext a
    simp only [splitSec, Pi.add_apply]
    rw [del_add (diff_mulVec hI hu' a) (diff_mulVec hL hq' a), ContinuousLinearMap.add_apply,
      del_mulVec hI hu' ξ a, del_mulVec hL hq' ξ a]
    simp [add_assoc]
  have e2 : ∀ η, secDbar (splitSec H u q) z η =
      incl m l *ᵥ (fun a => dbar (fun x => u x a) z η) +
        orthLift (H z) *ᵥ (fun a => dbar (fun x => q x a) z η) +
        mdbar (fun x => orthLift (H x)) z η *ᵥ q z := by
    intro η
    funext a
    simp only [secDbar, splitSec, Pi.add_apply]
    rw [dbar_add (diff_mulVec hI hu' a) (diff_mulVec hL hq' a), ContinuousLinearMap.add_apply,
      dbar_mulVec hI hu' η a, dbar_mulVec hL hq' η a]
    simp [add_assoc]
  have kP := orthProj_mul_covDel_orthLift h hs hz
  refine ⟨fun ξ => ?_, fun ξ => ?_, fun η => ?_, fun η => ?_⟩
  · have k : orthProj (H z) * mdel (fun x => orthLift (H x)) z ξ =
        -(orthProj (H z) * conn H z ξ * orthLift (H z)) := by
      rw [Matrix.mul_assoc, eq_neg_iff_add_eq_zero, ← Matrix.mul_add, kP]
    rw [e1, covDel, conn_gramS h hs hz]
    simp only [mulVec_add, mulVec_mulVec, orthProj_mul_incl, orthProj_mul_orthLift, one_mulVec,
      zero_mulVec, k, neg_mulVec, ← Matrix.mul_assoc]
    abel
  · rw [e1, covDel, conn_gramQ h hs hz, secondForm, blockQS]
    simp only [mulVec_add, mulVec_mulVec, quotMap_mul_incl, quotMap_mul_orthLift,
      quotMap_mul_mdel_orthLift, one_mulVec, zero_mulVec, ← Matrix.mul_assoc]
    abel
  · beta_reduce
    rw [e2, ← extForm_eq_neg_secondFormAdj hH1 (h.eventually_herm hz) hu hsz, extForm]
    simp only [mulVec_add, mulVec_mulVec, orthProj_mul_incl, orthProj_mul_orthLift, one_mulVec,
      zero_mulVec, add_zero]
    rfl
  · rw [e2]
    simp only [mulVec_add, mulVec_mulVec, quotMap_mul_incl, quotMap_mul_orthLift,
      quotMap_mul_mdbar_orthLift, one_mulVec, zero_mulVec, zero_add, add_zero]
    rfl

example : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l] {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H) (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U), ConnBlocks H z (fun η => -secondFormAdj H z η) (secondForm H z) := @connBlocks_secondForm

end GlobalTheory.SubQuotConn
