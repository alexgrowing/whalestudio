import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSelfDualE
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.ProdFormula
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ReductionLemmaSecond
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree

open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.GramMean

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def embGramDet {d j : ℕ} (H : Matrix (Fin d) (Fin d) K) (E : Matrix (Fin d) (Fin j) K)
    (φ : K →+* ℂ) : ℂ :=
  ((E.map φ)ᴴ * H.map φ * E.map φ).det

omit [NumberField K] [StarRing K] in
theorem embGramDet_conjugate {d j : ℕ} (H : Matrix (Fin d) (Fin d) K)
    (E : Matrix (Fin d) (Fin j) K) (φ : K →+* ℂ) :
    embGramDet H E (ComplexEmbedding.conjugate φ) = starRingEnd ℂ (embGramDet H E φ) := by
  have hm : ∀ {a b : ℕ} (M : Matrix (Fin a) (Fin b) K),
      M.map (ComplexEmbedding.conjugate φ) = (M.map φ).map (starRingEnd ℂ) := by
    intro a b M
    ext i k
    simp [ComplexEmbedding.conjugate_coe_eq]
  unfold embGramDet
  rw [hm E, hm H, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.map_mul]
  congr 2

omit [NumberField K] [StarRing K] in
theorem embGramDet_re_mk {d j : ℕ} (H : Matrix (Fin d) (Fin d) K)
    (E : Matrix (Fin d) (Fin j) K) (φ : K →+* ℂ) :
    (embGramDet H E (InfinitePlace.mk φ).embedding).re = (embGramDet H E φ).re := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · rw [h]
  · rw [h, embGramDet_conjugate, Complex.conj_re]

theorem gram_eq_mul {d j : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (v : InfinitePlace K) (e : Fin j → Fin d → K) :
    gram X v e = (((Matrix.of e)ᵀ).map v.embedding)ᴴ * (((X v)⁻¹)ᴴ * (X v)⁻¹) *
      ((Matrix.of e)ᵀ).map v.embedding := by
  ext a c
  simp only [gram, Formalism.HN.gramPl, Matrix.of_apply, majAt_eq, metMat, cv, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
    Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

theorem map_gramR {d j : ℕ} (H : Matrix (Fin d) (Fin d) K) (e : Fin j → Fin d → K)
    (φ : K →+* ℂ) :
    φ (gramR H e) = ((((Matrix.of e)ᵀ).map (Rb.tw φ))ᴴ * H.map φ *
      ((Matrix.of e)ᵀ).map φ).det := by
  unfold gramR
  rw [RingHom.map_det, RingHom.mapMatrix_apply]
  congr 1
  ext a b
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.transpose_apply, dotProduct, Matrix.mulVec, Pi.star_apply, map_sum, map_mul,
    Rb.tw_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [Complex.star_def, Complex.conj_conj]
  ring

private theorem det_gram_eq_embGramDet {K : Type} [Field K] [NumberField K] [StarRing K] {d j : ℕ}
    (H : Matrix (Fin d) (Fin d) K) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (hX : ∀ v : InfinitePlace K, ((X v)⁻¹)ᴴ * (X v)⁻¹ = H.map v.embedding)
    (e : Fin j → Fin d → K) (v : InfinitePlace K) :
    (gram X v e).det = embGramDet H ((Matrix.of e)ᵀ) v.embedding := by
  rw [gram_eq_mul, hX v]
  rfl

private theorem det_gram_re_nonneg' {K : Type} [Field K] [NumberField K] [StarRing K] {d j : ℕ}
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (hX : ∀ v : InfinitePlace K, IsUnit (X v).det)
    (e : Fin j → Fin d → K) (v : InfinitePlace K) : 0 ≤ (gram X v e).det.re := by
  have hP : (((X v)⁻¹)ᴴ * (X v)⁻¹).PosDef := Rb.metMat_posDef X v (hX v)
  have hS := hP.posSemidef.conjTranspose_mul_mul_same (((Matrix.of e)ᵀ).map v.embedding)
  rw [← gram_eq_mul] at hS
  exact (Complex.le_def.mp hS.det_nonneg).1

theorem prod_norm_gramR_le (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    (d j : ℕ) (H : Matrix (Fin d) (Fin d) K) (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ)
    (hR : IsRatHerm (cmMax K) H X) (e : Fin j → Fin d → K) :
    ∏ v : InfinitePlace K, ‖v.embedding (gramR H e)‖ ≤
      ∏ v : InfinitePlace K, (gram X v e).det.re := by
  have hU : ∀ v : InfinitePlace K, IsUnit (X v).det := fun v => (hR.2 v).1
  have hX : ∀ v : InfinitePlace K, ((X v)⁻¹)ᴴ * (X v)⁻¹ = H.map v.embedding := fun v => (hR.2 v).2
  have hK0 : IsCMSub (cmMax K) := fun σ a ha => ha σ
  set E : Matrix (Fin d) (Fin j) K := (Matrix.of e)ᵀ with hE
  set g : InfinitePlace K → ℝ := fun v => (gram X v e).det.re with hg
  have hg0 : ∀ v, 0 ≤ g v := fun v => det_gram_re_nonneg' X hU e v
  have hloc : ∀ v : InfinitePlace K, ‖v.embedding (gramR H e)‖ ^ 2 ≤ g (Rb.plc v) * g v := by
    intro v
    have hPD : (H.map v.embedding).PosDef := by
      rw [← hX v]; exact Rb.metMat_posDef X v (hU v)
    have hcs := determinant_cauchy_schwarz d j (H.map v.embedding) hPD ((E.map (Rb.tw v.embedding))ᴴ)
      ((E.map v.embedding)ᴴ)
    rw [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose] at hcs
    rw [map_gramR]
    have h1 : g (Rb.plc v) = (embGramDet H E (Rb.tw v.embedding)).re := by
      simp only [hg]
      rw [det_gram_eq_embGramDet H X hX e, Rb.plc, embGramDet_re_mk]
    have h2 : g v = (embGramDet H E v.embedding).re := by
      simp only [hg]
      rw [det_gram_eq_embGramDet H X hX e]
    rw [h1, h2]
    unfold embGramDet
    rw [Rb.Hmap_tw (cmMax K) hK0 H hR.1]
    exact hcs
  have hperm : ∏ v : InfinitePlace K, g (Rb.plc v) = ∏ v : InfinitePlace K, g v :=
    Equiv.prod_comp (Function.Involutive.toPerm _ (fun v => Rb.plc_plc v)) g
  have hsq : (∏ v : InfinitePlace K, ‖v.embedding (gramR H e)‖) ^ 2 ≤
      (∏ v : InfinitePlace K, g v) ^ 2 := by
    have hsq2 : (∏ v : InfinitePlace K, g v) ^ 2 = ∏ v : InfinitePlace K, (g (Rb.plc v) * g v) := by
      rw [Finset.prod_mul_distrib, hperm, sq]
    rw [← Finset.prod_pow, hsq2]
    exact Finset.prod_le_prod (fun v _ => by positivity) (fun v _ => hloc v)
  have ha : 0 ≤ ∏ v : InfinitePlace K, ‖v.embedding (gramR H e)‖ :=
    Finset.prod_nonneg fun v _ => norm_nonneg _
  have hb : 0 ≤ ∏ v : InfinitePlace K, g v := Finset.prod_nonneg fun v _ => hg0 v
  nlinarith

end GlobalTheory.GramMean
