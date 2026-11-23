import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HermitianCurvatureForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovariantSecondFundamentalForm
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
open Matrix Complex ComplexConjugate Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms

noncomputable section

namespace GlobalTheory.SubGauss

variable {m l : Type} [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq l]

theorem orthProj_transpose_mul_subGram (K : Matrix (m ⊕ l) (m ⊕ l) ℂ)
    (hs : IsUnit (subGram K).det) : (orthProj K)ᵀ * subGram K = K * incl m l := by
  have hc : (orthCoeff K)ᵀ = K.toBlocks₂₁ * K.toBlocks₁₁⁻¹ := by
    simp [orthCoeff, transpose_nonsing_inv]
  rw [orthProj, transpose_fromCols, transpose_one, fromRows_mul, hc,
    subGram, nonsing_inv_mul_cancel_right K.toBlocks₁₁ _ hs]
  conv_rhs => rw [← fromBlocks_toBlocks K]
  simp [incl, fromBlocks_mul_fromRows, subGram]

theorem incl_transpose_mul_mul (M : Matrix (m ⊕ l) (m ⊕ l) ℂ) :
    (incl m l)ᵀ * M * incl m l = M.toBlocks₁₁ := by
  conv_lhs => rw [← fromBlocks_toBlocks M]
  simp [incl, transpose_fromRows, fromCols_mul_fromBlocks, fromCols_mul_fromRows]

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V]
  [IsScalarTower ℝ ℂ V]

theorem conn_gramS {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {x : V} (hu : IsUnit (H x).det)
    (hs : IsUnit (subGram (H x)).det) (ξ : V) :
    conn (gramS H) x ξ = orthProj (H x) * (conn H x ξ * incl m l) := by
  refine (eq_conn_of_compatible (H := gramS H) hs ?_).symm
  have e : mdel (gramS H) x ξ = (mdel H x ξ).toBlocks₁₁ := by ext a b; rfl
  rw [e, ← incl_transpose_mul_mul, ← conn_transpose_mul hu, transpose_mul, transpose_mul,
    Matrix.mul_assoc, Matrix.mul_assoc, gramS, orthProj_transpose_mul_subGram _ hs]
  simp only [Matrix.mul_assoc]

theorem mContDiffAt_orthProj {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} {k : WithTop ℕ∞}
    (h : MContDiffAt k H z) (hs : IsUnit (subGram (H z)).det) :
    MContDiffAt k (fun x => orthProj (H x)) z := by
  have hc : MContDiffAt k (fun x => orthCoeff (H x)) z :=
    (h.subGram.transpose.inv (by rwa [det_transpose])).mul (h.submatrix Sum.inr Sum.inl).transpose
  rintro a (b | b)
  · simpa [orthProj] using (contDiffAt_const : ContDiffAt ℝ k (fun _ : V => (1 : Matrix m m ℂ) a b) z)
  · simpa [orthProj] using hc a b

theorem mdbar_orthProj {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : MContDiffAt 1 H z)
    (hh : ∀ᶠ x in 𝓝 z, (H x).IsHermitian) (hu : IsUnit (H z).det)
    (hs : IsUnit (subGram (H z)).det) (η : V) :
    mdbar (fun x => orthProj (H x)) z η = secondFormAdj H z η * quotMap m l := by
  have e1 : mdbar (fun x => orthProj (H x)) z η =
      fromCols 0 (mdbar (fun x => orthCoeff (H x)) z η) := by
    ext a (b | b) <;> simp [orthProj]
  have e2 : mdbar (fun x => orthCoeff (H x)) z η = secondFormAdj H z η := by
    rw [← neg_neg (mdbar _ z η), ← extForm_eq_neg_mdbar, extForm_eq_neg_secondFormAdj h hh hu hs,
      neg_neg]
  rw [e1, e2, quotMap, mul_fromCols]
  simp

theorem curv_gramS {U : Set V} {H : V → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : V} (h : IsHermFrame U H)
    (hs : ∀ x ∈ U, IsUnit (subGram (H x)).det) (hz : z ∈ U) (ξ η : V) :
    curv (gramS H) z ξ η = blockSS (H z) (curv H z ξ η) +
      wedgeAntiHol (secondFormAdj H z) (secondForm H z) ξ η := by
  have hU : U ∈ 𝓝 z := h.isOpen.mem_nhds hz
  have h2 := h.two hz
  have h1 := h.one hz
  have hθ : MContDiffAt 1 (fun x => conn H x ξ) z :=
    h2.conn (h.isUnit z hz) (by norm_num) ξ
  have hP : MContDiffAt 1 (fun x => orthProj (H x)) z := mContDiffAt_orthProj h1 (hs z hz)
  have he : (fun x => conn (gramS H) x ξ) =ᶠ[𝓝 z]
      fun x => orthProj (H x) * (conn H x ξ * incl m l) :=
    Filter.mem_of_superset hU fun x hx => conn_gramS (h.isUnit x hx) (hs x hx) ξ
  have hB : mdbar (fun x => conn H x ξ * incl m l) z η = mdbar (fun x => conn H x ξ) z η * incl m l := by
    rw [mdbar_mul hθ (mContDiffAt_const _), mdbar_const, Matrix.mul_zero, zero_add]
  rw [curv, mdbar_congr he, mdbar_mul hP (hθ.mul (mContDiffAt_const _)), hB,
    mdbar_orthProj h1 (h.eventually_herm hz) (h.isUnit z hz) (hs z hz), blockSS, curv,
    wedgeAntiHol, secondForm, blockQS]
  simp only [Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul, neg_add]

end GlobalTheory.SubGauss
