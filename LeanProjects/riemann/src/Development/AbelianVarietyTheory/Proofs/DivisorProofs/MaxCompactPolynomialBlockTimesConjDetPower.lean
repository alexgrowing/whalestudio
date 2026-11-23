import Development.AbelianVarietyTheory.Definitions.Divisors.DatumEquiv

section

noncomputable section

open MvPolynomial Matrix
open GlobalTheory.PsCo.Pc1 (Mat Poly ev blockAlg detbP)
open scoped ComplexConjugate

namespace GlobalTheory.PsCo.PcEF.BlockEvaluationOffDiagonal

variable {n : ℕ}

lemma ev_inl (k : Mat n) (a b : Fin n) : ev k (X (Sum.inl (a, b))) = k a b := by
  simp [GlobalTheory.PsCo.Pc1.ev]

lemma ev_inr (k : Mat n) (a b : Fin n) : ev k (X (Sum.inr (a, b))) = star (k a b) := by
  simp [GlobalTheory.PsCo.Pc1.ev]

lemma offdiag {ε : Fin n → Bool} {k : Mat n} (hk : k ∈ Formalism.REAL.Kset ε) {a b : Fin n} (hab : ε a ≠ ε b) :
    k a b = 0 := by
  have h := congrFun (congrFun hk.2 a) b
  simp only [Formalism.REAL.Jm, mul_diagonal, diagonal_mul] at h
  cases ha : ε a <;> cases hb : ε b <;> simp only [ha, hb, Bool.false_eq_true, if_false, if_true] at h hab
  · exact absurd rfl hab
  · linear_combination (1 / 2 : ℂ) * h
  · linear_combination (-1 / 2 : ℂ) * h
  · exact absurd rfl hab

def bM (ε : Fin n → Bool) : Matrix (Fin n) (Fin n) (blockAlg ε) := fun a b =>
  if h : ε a = ε b then ⟨X (Sum.inl (a, b)), Algebra.subset_adjoin ⟨a, b, h, rfl⟩⟩ else 0

def evB (ε : Fin n → Bool) (k : Mat n) : blockAlg ε →+* ℂ := (ev k).comp (blockAlg ε).val.toRingHom

lemma evB_apply (ε : Fin n → Bool) (k : Mat n) (x : blockAlg ε) : evB ε k x = ev k (x : Poly n) := rfl

lemma map_bM {ε : Fin n → Bool} {k : Mat n} (hk : k ∈ Formalism.REAL.Kset ε) : (bM ε).map (evB ε k) = k := by
  ext a b
  simp only [Matrix.map_apply, bM]
  split_ifs with h
  · rw [evB_apply, ev_inl]
  · rw [map_zero, offdiag hk h]

lemma det_bM {ε : Fin n → Bool} {k : Mat n} (hk : k ∈ Formalism.REAL.Kset ε) : evB ε k (bM ε).det = k.det := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, map_bM hk]

lemma adj_bM {ε : Fin n → Bool} {k : Mat n} (hk : k ∈ Formalism.REAL.Kset ε) (a b : Fin n) :
    evB ε k ((bM ε).adjugate a b) = k.adjugate a b := by
  have := congrFun (congrFun (RingHom.map_adjugate (evB ε k) (bM ε)) a) b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, map_bM hk] at this
  exact this

lemma ev_detbP (k : Mat n) : ev k (detbP n) = conj k.det := by
  rw [GlobalTheory.PsCo.Pc1.detbP, RingHom.map_det, (starRingEnd ℂ).map_det]
  congr 1
  ext a b
  simp [RingHom.mapMatrix_apply, ev_inr]

lemma conj_det_mul {ε : Fin n → Bool} {k : Mat n} (hk : k ∈ Formalism.REAL.Kset ε) : conj k.det * k.det = 1 := by
  have h := congrArg Matrix.det (Matrix.mem_unitaryGroup_iff'.mp hk.1)
  rw [Matrix.det_mul, Matrix.det_one, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose] at h
  simpa using h

lemma star_entry {ε : Fin n → Bool} {k : Mat n} (hk : k ∈ Formalism.REAL.Kset ε) (a b : Fin n) :
    star (k a b) = conj k.det * k.adjugate b a := by
  have hu : k * star k = 1 := Matrix.mem_unitaryGroup_iff.mp hk.1
  have h1 : k.adjugate * k = k.det • (1 : Mat n) := Matrix.adjugate_mul k
  have h2 : kᴴ = conj k.det • k.adjugate := by
    calc kᴴ = (conj k.det * k.det) • kᴴ := by rw [conj_det_mul hk, one_smul]
      _ = conj k.det • ((k.det • (1 : Mat n)) * kᴴ) := by rw [smul_mul_assoc, one_mul, smul_smul]
      _ = conj k.det • k.adjugate := by
        rw [← h1, Matrix.mul_assoc, ← Matrix.star_eq_conjTranspose, hu, Matrix.mul_one]
  have := congrFun (congrFun h2 b) a
  simpa [Matrix.conjTranspose_apply] using this

def dB (ε : Fin n → Bool) : Poly n := ((bM ε).det : Poly n)

lemma dB_mem (ε : Fin n → Bool) : dB ε ∈ blockAlg ε := (bM ε).det.2

lemma ev_dB {ε : Fin n → Bool} {k : Mat n} (hk : k ∈ Formalism.REAL.Kset ε) : ev k (dB ε) = k.det := det_bM hk

def Good (ε : Fin n → Bool) (P : Poly n) : Prop :=
  ∃ (M : ℕ) (Q : Poly n), Q ∈ blockAlg ε ∧ ∀ k ∈ Formalism.REAL.Kset ε, ev k P = ev k (detbP n ^ M * Q)

lemma good (ε : Fin n → Bool) (P : Poly n) : Good ε P := by
  refine MvPolynomial.induction_on P ?_ ?_ ?_
  · intro a
    refine ⟨0, C a, ?_, fun k _ => by simp⟩
    simpa [MvPolynomial.algebraMap_eq] using (blockAlg ε).algebraMap_mem a
  · rintro p q ⟨M1, Q1, h1, e1⟩ ⟨M2, Q2, h2, e2⟩
    refine ⟨M1 + M2, Q1 * dB ε ^ M2 + Q2 * dB ε ^ M1, ?_, fun k hk => ?_⟩
    · exact add_mem (mul_mem h1 (pow_mem (dB_mem ε) _)) (mul_mem h2 (pow_mem (dB_mem ε) _))
    · have hc : ∀ m : ℕ, conj k.det ^ m * k.det ^ m = 1 := fun m => by
        rw [← mul_pow, conj_det_mul hk, one_pow]
      rw [map_add, e1 k hk, e2 k hk]
      simp only [map_mul, map_pow, map_add, ev_detbP, ev_dB hk]
      rw [pow_add]
      linear_combination (-(conj k.det ^ M1 * ev k Q1)) * hc M2 + (-(conj k.det ^ M2 * ev k Q2)) * hc M1
  · rintro p i ⟨M, Q, hQ, e⟩
    rcases i with ⟨a, b⟩ | ⟨a, b⟩
    · refine ⟨M, Q * ((bM ε a b : blockAlg ε) : Poly n), mul_mem hQ (bM ε a b).2, fun k hk => ?_⟩
      have h : ev k ((bM ε a b : blockAlg ε) : Poly n) = k a b := by
        have := congrFun (congrFun (map_bM hk) a) b
        rw [Matrix.map_apply] at this
        exact this
      rw [map_mul, e k hk, ev_inl]
      simp only [map_mul, h]
      ring
    · refine ⟨M + 1, Q * (((bM ε).adjugate b a : blockAlg ε) : Poly n),
        mul_mem hQ ((bM ε).adjugate b a).2, fun k hk => ?_⟩
      have h : ev k (((bM ε).adjugate b a : blockAlg ε) : Poly n) = k.adjugate b a := adj_bM hk b a
      rw [map_mul, e k hk, ev_inr, star_entry hk]
      simp only [map_mul, map_pow, h, ev_detbP]
      ring

end GlobalTheory.PsCo.PcEF.BlockEvaluationOffDiagonal

namespace GlobalTheory.PsCo.PcEF

theorem maxCompactPolynomial_blockTimesConjDetPower : BlockForm := by
  intro n ε P
  exact BlockEvaluationOffDiagonal.good ε P

end GlobalTheory.PsCo.PcEF

end
end
