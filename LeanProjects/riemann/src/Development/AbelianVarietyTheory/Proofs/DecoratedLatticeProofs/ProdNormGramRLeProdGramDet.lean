import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
import Formalism.HarderNarasimhan.FinalCor
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.LocalToGlobal.Divisibility.FramesLemmas

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.DivisionValues
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory

namespace GramPlacesCS

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem map_gramR {n j : ℕ} (G : Matrix (Fin n) (Fin n) K) (e : Fin j → Fin n → K) (σ : K →+* ℂ) :
    σ (gramR G e) =
      ((StepBAux.fmat (Rb.tw σ) e)ᴴ * G.map σ * StepBAux.fmat σ e).det := by
  rw [gramR, RingHom.map_det]
  congr 1
  ext a b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, StepBAux.fmat, dotProduct, Matrix.mulVec, Pi.star_apply, map_sum,
    map_mul, Rb.tw_apply, Complex.star_def, Complex.conj_conj, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

omit [NumberField K] [StarRing K] in

theorem det_conjugate {n j : ℕ} (G : Matrix (Fin n) (Fin n) K) (e : Fin j → Fin n → K)
    (φ : K →+* ℂ) :
    ((StepBAux.fmat (ComplexEmbedding.conjugate φ) e)ᴴ * G.map (ComplexEmbedding.conjugate φ) *
        StepBAux.fmat (ComplexEmbedding.conjugate φ) e).det =
      starRingEnd ℂ (((StepBAux.fmat φ e)ᴴ * G.map φ * StepBAux.fmat φ e).det) := by
  have hE : StepBAux.fmat (ComplexEmbedding.conjugate φ) e =
      (StepBAux.fmat φ e).map (starRingEnd ℂ) := by
    ext i a; simp [StepBAux.fmat, ComplexEmbedding.conjugate_coe_eq]
  have hG : G.map (ComplexEmbedding.conjugate φ) = (G.map φ).map (starRingEnd ℂ) := by
    ext i a; simp [ComplexEmbedding.conjugate_coe_eq]
  rw [hE, hG, Rb.conjT_map_conj, ← Matrix.map_mul, ← Matrix.map_mul,
    RingHom.map_det, RingHom.mapMatrix_apply]

theorem gram_eq (K0 : Subfield K) {n j : ℕ} (G : Matrix (Fin n) (Fin n) K)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hX : IsRatHerm K0 G X)
    (e : Fin j → Fin n → K) (v : InfinitePlace K) :
    gram X v e =
      (StepBAux.fmat v.embedding e)ᴴ * G.map v.embedding * StepBAux.fmat v.embedding e := by
  rw [StepBAux.gram_eq_fmat, StepBAux.met, (hX.2 v).2]

theorem gram_mk_re (K0 : Subfield K) {n j : ℕ} (G : Matrix (Fin n) (Fin n) K)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hX : IsRatHerm K0 G X)
    (e : Fin j → Fin n → K) (φ : K →+* ℂ) :
    (gram X (InfinitePlace.mk φ) e).det.re =
      ((StepBAux.fmat φ e)ᴴ * G.map φ * StepBAux.fmat φ e).det.re := by
  rw [gram_eq K0 G X hX]
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · rw [h]
  · rw [h, det_conjugate, Complex.conj_re]

theorem map_posDef (K0 : Subfield K) {n : ℕ} (G : Matrix (Fin n) (Fin n) K)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hX : IsRatHerm K0 G X)
    (v : InfinitePlace K) : (G.map v.embedding).PosDef := by
  rw [← (hX.2 v).2]
  exact Rb.metMat_posDef X v (hX.2 v).1

theorem gram_det_re_nonneg (K0 : Subfield K) {n j : ℕ} (G : Matrix (Fin n) (Fin n) K)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hX : IsRatHerm K0 G X)
    (e : Fin j → Fin n → K) (v : InfinitePlace K) : 0 ≤ (gram X v e).det.re := by
  rw [gram_eq K0 G X hX]
  have h := ((map_posDef K0 G X hX v).posSemidef.conjTranspose_mul_mul_same
    (StepBAux.fmat v.embedding e)).det_nonneg
  exact (Complex.le_def.mp h).1

theorem place_sq_le (K0 : Subfield K) (hK0 : IsCMSub K0) {n j : ℕ} (G : Matrix (Fin n) (Fin n) K)
    (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hX : IsRatHerm K0 G X)
    (e : Fin j → Fin n → K) (v : InfinitePlace K) :
    ‖v.embedding (gramR G e)‖ ^ 2 ≤ (gram X (Rb.plc v) e).det.re * (gram X v e).det.re := by
  have h := determinant_cauchy_schwarz n j _ (map_posDef K0 G X hX v)
    (StepBAux.fmat (Rb.tw v.embedding) e)ᴴ (StepBAux.fmat v.embedding e)ᴴ
  simp only [Matrix.conjTranspose_conjTranspose] at h
  rw [map_gramR, Rb.plc, gram_mk_re K0 G X hX, Rb.Hmap_tw K0 hK0 G hX.1, gram_eq K0 G X hX]
  exact h

end GramPlacesCS

open GramPlacesCS in

theorem prod_norm_gramR_le_prod_gram_det :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (K0 : Subfield K), IsCMSub K0 →
    ∀ (n j : ℕ) (G : Matrix (Fin n) (Fin n) K) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ),
    IsRatHerm K0 G X → ∀ e : Fin j → Fin n → K,
      ∏ v : InfinitePlace K, ‖v.embedding (gramR G e)‖ ≤
        ∏ v : InfinitePlace K, (gram X v e).det.re := by
  intro K _ _ _ K0 hK0 n j G X hX e
  have hperm : ∏ v : InfinitePlace K, (gram X (Rb.plc v) e).det.re =
      ∏ v : InfinitePlace K, (gram X v e).det.re :=
    Equiv.prod_comp (Function.Involutive.toPerm _ Rb.plc_plc) (fun v => (gram X v e).det.re)
  have hsq : (∏ v : InfinitePlace K, ‖v.embedding (gramR G e)‖) ^ 2 ≤
      (∏ v : InfinitePlace K, (gram X v e).det.re) ^ 2 := by
    calc (∏ v : InfinitePlace K, ‖v.embedding (gramR G e)‖) ^ 2
        = ∏ v : InfinitePlace K, ‖v.embedding (gramR G e)‖ ^ 2 := (Finset.prod_pow _ _ _).symm
      _ ≤ ∏ v : InfinitePlace K, ((gram X (Rb.plc v) e).det.re * (gram X v e).det.re) :=
        Finset.prod_le_prod (fun v _ => by positivity) (fun v _ => place_sq_le K0 hK0 G X hX e v)
      _ = (∏ v : InfinitePlace K, (gram X v e).det.re) ^ 2 := by
        rw [Finset.prod_mul_distrib, hperm, sq]
  exact (pow_le_pow_iff_left₀ (Finset.prod_nonneg fun v _ => norm_nonneg _)
    (Finset.prod_nonneg fun v _ => gram_det_re_nonneg K0 G X hX e v) two_ne_zero).mp hsq

end GlobalTheory
