import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HermitianCurvatureForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovariantSecondFundamentalForm
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

noncomputable section

namespace GlobalTheory.GaussQuot

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]

theorem quotMap_conjTranspose : (quotMap m l)ᴴ = (quotMap m l)ᵀ := by
  ext (a | a) b <;> simp [quotMap, Matrix.one_apply, apply_ite]

theorem quotMap_mul_conj_orthLift (H : Matrix (m ⊕ l) (m ⊕ l) ℂ) :
    quotMap m l * (orthLift H)ᴴᵀ = 1 := by
  have h := congrArg (fun M => (Mᴴ)ᵀ) (quotMap_mul_orthLift H)
  simp only [conjTranspose_mul, transpose_mul, conjTranspose_one, transpose_one] at h
  rw [← h, quotMap_conjTranspose, transpose_transpose]

theorem orthLift_transpose_mul_eq {H : Matrix (m ⊕ l) (m ⊕ l) ℂ} (hs : IsUnit (subGram H).det) :
    (orthLift H)ᵀ * H = quotGram H * quotMap m l := by
  rw [orthLift_transpose_mul hs, quotMap, mul_fromCols]; simp

theorem mul_conj_orthLift {H : Matrix (m ⊕ l) (m ⊕ l) ℂ} (hh : H.IsHermitian)
    (hs : IsUnit (subGram H).det) : H * (orthLift H)ᴴᵀ = (quotMap m l)ᵀ * quotGram H := by
  have h := congrArg conjTranspose (orthLift_transpose_mul_eq hs)
  simp only [conjTranspose_mul, hh.eq, (isHermitian_quotGram hh).eq, quotMap_conjTranspose] at h
  exact h

theorem mul_mdel_eq_zero {p : Type} [Fintype p] {P : Matrix l p ℂ} {L : V → Matrix p l ℂ} {x : V}
    (hL : MContDiffAt 1 L x) (h1 : ∀ y, P * L y = 1) (ξ : V) : P * mdel L x ξ = 0 := by
  have h := mdel_mul (mContDiffAt_const P) hL ξ (z := x)
  rw [show (fun y => P * L y) = fun _ => (1 : Matrix l l ℂ) from funext h1, mdel_const,
    mdel_const, Matrix.zero_mul, add_zero] at h
  exact h.symm

theorem mul_mdbar_eq_zero {p : Type} [Fintype p] {P : Matrix l p ℂ} {L : V → Matrix p l ℂ} {x : V}
    (hL : MContDiffAt 1 L x) (h1 : ∀ y, P * L y = 1) (η : V) : P * mdbar L x η = 0 := by
  have h := mdbar_mul (mContDiffAt_const P) hL η (z := x)
  rw [show (fun y => P * L y) = fun _ => (1 : Matrix l l ℂ) from funext h1, mdbar_const,
    mdbar_const, Matrix.zero_mul, add_zero] at h
  exact h.symm

theorem conn_gramQ {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {x : V} (h1 : MContDiffAt 1 H x)
    (hh : (H x).IsHermitian) (hu : IsUnit (H x).det) (hs : IsUnit (subGram (H x)).det) (ξ : V) :
    conn (gramQ H) x ξ = quotMap m l * conn H x ξ * orthLift (H x) := by
  symm
  refine eq_conn_of_compatible (H := gramQ H) (z := x) (ξ := ξ)
    (show IsUnit (gramQ H x).det from isUnit_det_quotGram hu hs) ?_
  have hL : MContDiffAt 1 (fun y => orthLift (H y)) x := GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.mContDiffAt_orthLift h1 hs
  have hL' : MContDiffAt 1 (fun y => (orthLift (H y))ᴴᵀ) x := hL.conjTranspose.transpose
  have hev : gramQ H =ᶠ[𝓝 x] fun y => (orthLift (H y))ᵀ * H y * (orthLift (H y))ᴴᵀ := by
    filter_upwards [h1.subGram.eventually_isUnit hs] with y hy
    rw [orthLift_transpose_mul_eq hy, Matrix.mul_assoc, quotMap_mul_conj_orthLift, Matrix.mul_one]
    rfl
  have e0 : (mdel (fun y => orthLift (H y)) x ξ)ᵀ * H x * (orthLift (H x))ᴴᵀ = 0 := by
    rw [Matrix.mul_assoc, mul_conj_orthLift hh hs, ← Matrix.mul_assoc, ← transpose_mul,
      mul_mdel_eq_zero hL fun _ => quotMap_mul_orthLift _, transpose_zero, Matrix.zero_mul]
  have e2 : (orthLift (H x))ᵀ * H x * mdel (fun y => (orthLift (H y))ᴴᵀ) x ξ = 0 := by
    rw [orthLift_transpose_mul_eq hs, Matrix.mul_assoc,
      mul_mdel_eq_zero hL' fun _ => quotMap_mul_conj_orthLift _, Matrix.mul_zero]
  have e1 : mdel (gramQ H) x ξ = (orthLift (H x))ᵀ * mdel H x ξ * (orthLift (H x))ᴴᵀ := by
    rw [mdel_congr hev, mdel_mul (hL.transpose.mul h1) hL', mdel_mul hL.transpose h1, e2,
      zero_add, Matrix.add_mul, mdel_transpose, e0, add_zero]
  rw [e1, ← conn_transpose_mul hu, transpose_mul, transpose_mul, Matrix.mul_assoc,
    Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc, mul_conj_orthLift hh hs]
  rfl

theorem curv_gramQ {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H)
    (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ η : V) :
    curv (gramQ H) z ξ η = blockQQ (H z) (curv H z ξ η) +
      wedgeHolAnti (secondForm H z) (secondFormAdj H z) ξ η := by
  have hc : MContDiffAt 1 (fun x => conn H x ξ) z :=
    (h.two hz).conn (h.isUnit z hz) (by norm_num) ξ
  have hL : MContDiffAt 1 (fun x => orthLift (H x)) z :=
    GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.mContDiffAt_orthLift (h.one hz) (hs z hz)
  have hev : (fun x => conn (gramQ H) x ξ) =ᶠ[𝓝 z]
      fun x => quotMap m l * conn H x ξ * orthLift (H x) := by
    filter_upwards [h.isOpen.mem_nhds hz] with x hx
    exact conn_gramQ (h.one hx) (h.herm x hx) (h.isUnit x hx) (hs x hx) ξ
  have hd : mdbar (fun x => orthLift (H x)) z η = incl m l * extForm H z η := by
    have e := congrArg (· * mdbar (fun x => orthLift (H x)) z η) (incl_mul_orthProj_add (H z))
    simp only [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc,
      mul_mdbar_eq_zero hL (fun _ => quotMap_mul_orthLift _), Matrix.mul_zero, add_zero] at e
    rw [extForm, e]
  have hb : extForm H z η = -secondFormAdj H z η :=
    extForm_eq_neg_secondFormAdj (h.one hz) (h.eventually_herm hz) (h.isUnit z hz) (hs z hz) η
  rw [curv, mdbar_congr hev, mdbar_mul ((mContDiffAt_const _).mul hc) hL,
    mdbar_mul (mContDiffAt_const _) hc, mdbar_const, Matrix.zero_mul, add_zero, hd, hb,
    blockQQ, curv, wedgeHolAnti, secondForm, blockQS]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc, neg_add, neg_neg]
  abel

end GlobalTheory.GaussQuot
