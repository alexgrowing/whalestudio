import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HermitianCurvatureForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovariantSecondFundamentalForm
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
import Development.AbelianVarietyTheory.Definitions.Divisors.CurvSubQuotTautPairGram
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

noncomputable section

namespace GlobalTheory.CurvSQ

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V] {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]

theorem orthLift_transpose_mul_incl {T : Matrix (m ⊕ l) (m ⊕ l) ℂ} (hu : IsUnit (subGram T).det) :
    (orthLift T)ᵀ * T * incl m l = 0 := by
  rw [orthLift_transpose_mul hu]; simp [incl, fromCols_mul_fromRows]

theorem mul_incl_eq {T : Matrix (m ⊕ l) (m ⊕ l) ℂ} (hu : IsUnit (subGram T).det) :
    T * incl m l = (orthProj T)ᵀ * subGram T := by
  have hu' : IsUnit T.toBlocks₁₁ᵀ.det := by rwa [det_transpose]
  conv_lhs => rw [← fromBlocks_toBlocks T]
  rw [incl, fromBlocks_mul_fromRows, orthProj, transpose_fromCols, fromRows_mul, orthCoeff,
    transpose_mul, transpose_transpose, transpose_nonsing_inv, transpose_transpose, subGram,
    Matrix.mul_assoc, nonsing_inv_mul _ (show IsUnit T.toBlocks₁₁.det from hu)]
  simp

theorem mdel_orthLift (H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z ξ : V) :
    mdel (fun x => orthLift (H x)) z ξ = fromRows (-mdel (fun x => orthCoeff (H x)) z ξ) 0 := by
  ext (a | a) b <;> simp [orthLift, del_neg]

theorem mdbar_orthLift (H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z η : V) :
    mdbar (fun x => orthLift (H x)) z η = incl m l * extForm H z η := by
  have h : mdbar (fun x => orthLift (H x)) z η =
      fromRows (-mdbar (fun x => orthCoeff (H x)) z η) 0 := by
    ext (a | a) b <;> simp [orthLift, dbar_neg]
  rw [extForm, h, orthProj, fromCols_mul_fromRows, incl, fromRows_mul]
  simp

theorem quotMap_mul_mdel_orthLift (H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z ξ : V) :
    quotMap m l * mdel (fun x => orthLift (H x)) z ξ = 0 := by
  rw [mdel_orthLift, quotMap, fromCols_mul_fromRows]; simp

theorem mdel_orthProj_mul_incl (H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ) (z ξ : V) :
    mdel (fun x => orthProj (H x)) z ξ * incl m l = 0 := by
  have h : mdel (fun x => orthProj (H x)) z ξ = fromCols 0 (mdel (fun x => orthCoeff (H x)) z ξ) := by
    ext a (b | b) <;> simp [orthProj]
  rw [h, incl, fromCols_mul_fromRows]; simp

variable {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ}

theorem mContDiffAt_orthProj {k : WithTop ℕ∞} {z : V} (h : MContDiffAt k H z)
    (hs : IsUnit (subGram (H z)).det) : MContDiffAt k (fun x => orthProj (H x)) z := by
  have hc := GlobalTheory.HermFrame.Model.mContDiffAt_orthCoeff h hs
  rintro a (b | b)
  exacts [contDiffAt_const, hc a b]

theorem orthProj_mul_covDel_orthLift (h : IsHermFrame U H)
    (hs : ∀ z ∈ U, IsUnit (subGram (H z)).det) {x : V} (hx : x ∈ U) (ξ : V) :
    orthProj (H x) * (mdel (fun y => orthLift (H y)) x ξ + conn H x ξ * orthLift (H x)) = 0 := by
  have hL : MContDiffAt 1 (fun y => orthLift (H y)) x :=
    GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.mContDiffAt_orthLift (h.one hx) (hs x hx)
  have hA : MContDiffAt 1 (fun y => (orthLift (H y))ᵀ * H y) x := hL.transpose.mul (h.one hx)
  have hB : MContDiffAt 1 (fun _ : V => incl m l) x := mContDiffAt_const _
  have e0 : mdel (fun y => (orthLift (H y))ᵀ * H y * incl m l) x ξ = 0 := by
    rw [mdel_congr (B := fun _ => (0 : Matrix l m ℂ)) (mem_of_superset (h.isOpen.mem_nhds hx)
      fun y hy => orthLift_transpose_mul_incl (hs y hy)), mdel_const]
  rw [mdel_mul hA hB, mdel_const, Matrix.mul_zero, zero_add, mdel_mul hL.transpose (h.one hx),
    mdel_transpose, ← conn_transpose_mul (h.isUnit x hx)] at e0
  have e1 : (orthProj (H x) * (mdel (fun y => orthLift (H y)) x ξ +
      conn H x ξ * orthLift (H x)))ᵀ * subGram (H x) = 0 := by
    rw [transpose_mul, Matrix.mul_assoc, ← mul_incl_eq (hs x hx), ← e0, transpose_add,
      transpose_mul]
    simp only [Matrix.add_mul, Matrix.mul_assoc]
    abel
  have e2 := congrArg (· * (subGram (H x))⁻¹) e1
  simp only [Matrix.mul_assoc, mul_nonsing_inv _ (hs x hx), Matrix.mul_one, Matrix.zero_mul] at e2
  exact transpose_eq_zero.1 e2

theorem covDel_orthLift (h : IsHermFrame U H) (hs : ∀ z ∈ U, IsUnit (subGram (H z)).det)
    {x : V} (hx : x ∈ U) (ξ : V) :
    mdel (fun y => orthLift (H y)) x ξ + conn H x ξ * orthLift (H x) =
      orthLift (H x) * blockQQ (H x) (conn H x ξ) := by
  calc _ = (incl m l * orthProj (H x) + orthLift (H x) * quotMap m l) *
        (mdel (fun y => orthLift (H y)) x ξ + conn H x ξ * orthLift (H x)) := by
          rw [incl_mul_orthProj_add, Matrix.one_mul]
    _ = _ := by
      rw [Matrix.add_mul, Matrix.mul_assoc, orthProj_mul_covDel_orthLift h hs hx,
        Matrix.mul_zero, zero_add, Matrix.mul_assoc, Matrix.mul_add,
        quotMap_mul_mdel_orthLift, zero_add, blockQQ, Matrix.mul_assoc]

theorem blockSQ_curv_eq_covDelAnti_extForm {z : V} (h : IsHermFrame U H)
    (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ η : V) :
    blockSQ (H z) (curv H z ξ η) = covDelAnti (gramQ H) (gramS H) (extForm H) z ξ η := by
  have hu := h.isUnit z hz
  have hsz := hs z hz
  have hL2 : MContDiffAt 2 (fun x => orthLift (H x)) z :=
    GlobalTheory.IndefiniteRowSideFullHecke.CovariantSecondFundamentalForm.mContDiffAt_orthLift (h.two hz) hsz
  have hL1 : MContDiffAt 1 (fun x => orthLift (H x)) z := hL2.of_le one_le_two
  have hP1 : MContDiffAt 1 (fun x => orthProj (H x)) z := mContDiffAt_orthProj (h.one hz) hsz
  have hc : MContDiffAt 1 (fun x => conn H x ξ) z := (h.two hz).conn hu (by norm_num) ξ
  have hdL : MContDiffAt 1 (fun x => mdel (fun y => orthLift (H y)) x ξ) z :=
    hL2.mdel (by norm_num) ξ
  have hbL : MContDiffAt 1 (fun x => mdbar (fun y => orthLift (H y)) x η) z :=
    hL2.mdbar (by norm_num) η
  have hM : MContDiffAt 1 (fun x => blockQQ (H x) (conn H x ξ)) z :=
    ((mContDiffAt_const _).mul hc).mul hL1
  have he : (fun x => mdel (fun y => orthLift (H y)) x ξ + conn H x ξ * orthLift (H x)) =ᶠ[𝓝 z]
      fun x => orthLift (H x) * blockQQ (H x) (conn H x ξ) :=
    mem_of_superset (h.isOpen.mem_nhds hz) fun x hx => covDel_orthLift h hs hx ξ
  have F1 := mdbar_congr he η
  rw [mdbar_add hdL (hc.mul hL1), mdbar_mdel hL2, mdbar_mul hc hL1, mdbar_mul hL1 hM] at F1
  have cS : conn (gramS H) z ξ = blockSS (H z) (conn H z ξ) :=
    GlobalTheory.HermFrame.Model.conn_sub hu hsz ξ
  have cQ : conn (gramQ H) z ξ = blockQQ (H z) (conn H z ξ) :=
    GlobalTheory.HermFrame.Model.conn_quot (h.one hz) hu hsz ξ
  have kB : mdbar (fun x => orthLift (H x)) z η =
      incl m l * (orthProj (H z) * mdbar (fun x => orthLift (H x)) z η) := mdbar_orthLift H z η
  have k1 : orthProj (H z) * mdbar (fun x => conn H x ξ) z η * orthLift (H z) =
      orthProj (H z) * mdbar (fun x => orthLift (H x)) z η * blockQQ (H z) (conn H z ξ)
        - orthProj (H z) * mddbar (fun x => orthLift (H x)) z ξ η
        - orthProj (H z) * conn H z ξ * mdbar (fun x => orthLift (H x)) z η := by
    have e := congrArg (orthProj (H z) * ·) F1
    simp only [Matrix.mul_add] at e
    rw [← Matrix.mul_assoc (orthProj (H z)) (orthLift (H z)), orthProj_mul_orthLift,
      Matrix.zero_mul, zero_add] at e
    simp only [Matrix.mul_assoc]
    rw [← e]
    abel
  have k2 : mdel (fun x => orthProj (H x)) z ξ * mdbar (fun x => orthLift (H x)) z η = 0 := by
    rw [kB, ← Matrix.mul_assoc, mdel_orthProj_mul_incl, Matrix.zero_mul]
  have k3 : orthProj (H z) * conn H z ξ * mdbar (fun x => orthLift (H x)) z η =
      orthProj (H z) * conn H z ξ * incl m l *
        (orthProj (H z) * mdbar (fun x => orthLift (H x)) z η) := by
    conv_lhs => rw [kB]
    simp only [Matrix.mul_assoc]
  simp only [covDelAnti, homDel, extForm]
  rw [mdel_mul hP1 hbL, mdel_mdbar hL2, k2, add_zero, cS, cQ, blockSQ, curv, Matrix.mul_neg,
    Matrix.neg_mul, k1, k3, blockSS]
  simp only [Matrix.mul_assoc]
  abel

end GlobalTheory.CurvSQ
