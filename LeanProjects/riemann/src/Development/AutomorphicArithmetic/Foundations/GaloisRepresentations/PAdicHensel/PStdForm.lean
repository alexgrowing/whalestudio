import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.AuxiliaryInertOddPrime
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1 UpperTheory.Gal.Int.Geo GlobalTheory.CongL
open scoped TensorProduct

private lemma c_re_neg {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (τ : E →+* ℂ)
    (h : InfinitePlace.mk τ = InfinitePlace.mk A.τ₀) : (τ (A.c : E)).re < 0 := by
  rcases InfinitePlace.mk_eq_iff.mp h with h | h
  · rw [h]; exact A.c_neg
  · have h1 := A.c_neg
    rw [← h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_re] at h1
    exact h1

private lemma dg_ne {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (i : Fin n) :
    ((A.dg n i : 𝓞 E) : E) ≠ 0 := by
  have := A.c_ne
  unfold Arith.dg
  split_ifs <;> simp [this]

private lemma dg_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (i : Fin n) :
    cj E ((A.dg n i : 𝓞 E) : E) = ((A.dg n i : 𝓞 E) : E) := by
  have h : A.bar (A.dg n i) = A.dg n i := by
    unfold Arith.dg
    split_ifs <;> simp [A.c_real]
  exact (A.bar_eq _).symm.trans (congrArg _ h)

private lemma hd_cj {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (i : Fin n) :
    cj E ((A.hd n i : 𝓞 E) : E) = ((A.hd n i : 𝓞 E) : E) := by
  have h : A.bar (A.hd n i) = A.hd n i := by
    unfold Arith.hd Arith.dg
    split_ifs <;> simp [A.c_real]
  exact (A.bar_eq _).symm.trans (congrArg _ h)

private lemma hd_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (i : Fin n) :
    ((A.hd n i : 𝓞 E) : E) = -(A.c : E) * ((A.dg n i : 𝓞 E) : E) := by
  simp [Arith.hd]

private lemma re_form {n : ℕ} (a : ℂ) (x : Fin n → ℂ) :
    (star x ⬝ᵥ ((Matrix.diagonal fun _ => a) *ᵥ x)).re = a.re * ∑ i, Complex.normSq (x i) := by
  simp only [dotProduct, Matrix.mulVec_diagonal, Pi.star_apply, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : star (x i) * (a * x i) = a * ((Complex.normSq (x i) : ℝ) : ℂ) := by
    rw [Complex.normSq_eq_conj_mul_self]
    simp only [Complex.star_def]
    ring
  rw [h, Complex.re_mul_ofReal]

private lemma sum_pos' {n : ℕ} {x : Fin n → ℂ} (hx : x ≠ 0) : 0 < ∑ i, Complex.normSq (x i) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
    ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hi⟩

private lemma form_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (e : E →+* ℂ) :
    ((A.H n).map e)ᵀ * (Matrix.diagonal fun i => ((A.dg n i : 𝓞 E) : E)⁻¹).map e =
      Matrix.diagonal fun _ => -e (A.c : E) := by
  unfold Arith.H
  rw [Matrix.diagonal_map (map_zero _), Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rw [hd_eq, map_mul, map_neg, map_inv₀, mul_assoc, mul_inv_cancel₀ ((map_ne_zero e).2 (dg_ne A n i)), mul_one]

private lemma sym_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) :
    ((A.H n).map (cj E))⁻¹ * ((Matrix.diagonal fun i => ((A.dg n i : 𝓞 E) : E)).map (cj E))ᵀ * (A.H n).map (cj E) =
      Matrix.diagonal fun i => ((A.dg n i : 𝓞 E) : E) := by
  have hH : (A.H n).map (cj E) = A.H n := by
    unfold Arith.H
    rw [Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    exact hd_cj A n i
  have hD : (Matrix.diagonal fun i => ((A.dg n i : 𝓞 E) : E)).map (cj E) =
      Matrix.diagonal fun i => ((A.dg n i : 𝓞 E) : E) := by
    rw [Matrix.diagonal_map (map_zero _)]
    congr 1
    funext i
    exact dg_cj A n i
  have hu : IsUnit (A.H n).det := (A.det_ne n).isUnit
  have hc : (Matrix.diagonal fun i => ((A.dg n i : 𝓞 E) : E)) * A.H n =
      A.H n * Matrix.diagonal fun i => ((A.dg n i : 𝓞 E) : E) := by
    unfold Arith.H
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    ring
  rw [hH, hD, Matrix.diagonal_transpose, Matrix.mul_assoc, hc, Matrix.nonsing_inv_mul_cancel_left _ _ hu]

theorem UpperTheory.Gal.G1.pStdForm :
    HdSign → StdForm := by
  intro _ E _ _ _ A n p _ S
  have h1 : (Matrix.diagonal fun i => ((A.dg n i : 𝓞 E) : E)) * (Matrix.diagonal fun i => ((A.dg n i : 𝓞 E) : E)⁻¹) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (dg_ne A n i)
  have h2 : (Matrix.diagonal fun i => ((A.dg n i : 𝓞 E) : E)⁻¹) * (Matrix.diagonal fun i => ((A.dg n i : 𝓞 E) : E)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (dg_ne A n i)
  let β : S.G.Cˣ := (⟨Matrix.diagonal fun i => ((A.dg n i : 𝓞 E) : E), Matrix.diagonal fun i => ((A.dg n i : 𝓞 E) : E)⁻¹, h1, h2⟩ :
    (Matrix (Fin n) (Fin n) E)ˣ)
  refine ⟨β, rfl, sym_eq A n, ?_⟩
  intro v x hx
  have hs : sigPosH (S.G.gram_herm v) = sigPos (A.herm n) v.embedding := rfl
  have hf : S.G.gram v * S.G.psi v ((β⁻¹ : S.G.Cˣ) : S.G.C) = Matrix.diagonal fun _ => -v.embedding (A.c : E) :=
    form_eq A n v.embedding
  have hP := sum_pos' hx
  rw [hf, re_form, hs, Complex.neg_re]
  by_cases hm : InfinitePlace.mk v.embedding = InfinitePlace.mk A.τ₀
  · have hc := c_re_neg A v.embedding hm
    have h1' := ((S.sig v.embedding).1 hm).1
    exact ⟨fun _ => mul_pos (neg_pos.2 hc) hP, fun h => absurd h1' h⟩
  · have hc := A.c_pos v.embedding hm
    have h0 := ((S.sig v.embedding).2 hm).1
    refine ⟨fun h => ?_, fun _ => mul_neg_of_neg_of_pos (neg_neg_of_pos hc) hP⟩
    rw [h0] at h
    exact absurd h (by norm_num)
