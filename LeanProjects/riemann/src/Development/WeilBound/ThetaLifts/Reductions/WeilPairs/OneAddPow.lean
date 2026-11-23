import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.IntegralMul
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.PhaseFourierInjectivity

open PositivityTheory.ThKW.ModulusFactorDefinition

section

variable {R : Type} [CommRing R] {n : ℕ}

abbrev aC (R : Type) [CommRing R] (n : ℕ) : Matrix (Fin (n + n)) (Fin n) R :=
  (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (-1)).submatrix finSumFinEquiv.symm id

theorem CC_add : dC R n * (dC R n)ᵀ + aC R n * (aC R n)ᵀ = (2 : R) • 1 := by
  ext i j
  obtain ⟨p, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨q, rfl⟩ := finSumFinEquiv.surjective j
  simp only [diagCols, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, id, Matrix.smul_apply, Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq]
  rcases p with p | p <;> rcases q with q | q <;> simp [Matrix.one_apply] <;> split_ifs <;>
    first | (simp_all; done) | (simp_all; norm_num; done) | norm_num

theorem C_D (J : Matrix (Fin n) (Fin n) R) :
    (dC R n)ᵀ * (dbl J).submatrix finSumFinEquiv.symm finSumFinEquiv.symm = J * (aC R n)ᵀ := by
  rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.transpose_submatrix, diagCols, dbl,
    Matrix.transpose_fromRows, Matrix.transpose_fromRows, Matrix.fromCols_mul_fromBlocks]
  ext i j
  obtain ⟨q, rfl⟩ := finSumFinEquiv.surjective j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
  rcases q with q | q <;> simp [Matrix.one_apply]

theorem A_D (J : Matrix (Fin n) (Fin n) R) :
    (aC R n)ᵀ * (dbl J).submatrix finSumFinEquiv.symm finSumFinEquiv.symm = J * (dC R n)ᵀ := by
  rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.transpose_submatrix, diagCols, dbl,
    Matrix.transpose_fromRows, Matrix.transpose_fromRows, Matrix.fromCols_mul_fromBlocks]
  ext i j
  obtain ⟨q, rfl⟩ := finSumFinEquiv.surjective j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
  rcases q with q | q <;> simp [Matrix.one_apply]

theorem A_C : (aC R n)ᵀ * dC R n = 0 := by
  rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, diagCols, Matrix.transpose_fromRows,
    Matrix.fromCols_mul_fromRows]
  simp

theorem C_A : (dC R n)ᵀ * aC R n = 0 := by
  have := congrArg Matrix.transpose (A_C (R := R) (n := n))
  rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] at this

theorem ring_facts {A : Type} [Ring A] [Algebra R A] {Q Q' D N : A} {x y : R} (hxy : x * y = 1) (h1 : Q + Q' = 1)
    (hQ : Q * Q' = 0) (hQ' : Q' * Q = 0) :
    (x • Q + y • Q') * (y • Q + x • Q') = 1 ∧
    (Q * D * Q = 0 → Q' * D * Q' = 0 → (x • Q + y • Q') * D * (x • Q + y • Q') = D) ∧
    (N * Q = 0 → Q' * N = 0 → N * N = 0 ∧ (x • Q + y • Q') * N * (y • Q + x • Q') = (x * x) • N) := by
  have e1 : Q * Q = Q := by
    have := congrArg (Q * ·) h1
    simpa only [mul_add, hQ, add_zero, mul_one] using this
  have e2 : Q' * Q' = Q' := by
    have := congrArg (Q' * ·) h1
    simpa only [mul_add, hQ', zero_add, mul_one] using this
  have hyx : y * x = 1 := by rw [mul_comm, hxy]
  refine ⟨?_, fun a b => ?_, fun a b => ?_⟩
  · simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, e1, e2, hQ, hQ', smul_zero, add_zero, zero_add,
      hxy, hyx, one_smul, h1]
  · have hD : D = (Q + Q') * D * (Q + Q') := by rw [h1, one_mul, mul_one]
    conv_rhs => rw [hD]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, a, b, smul_zero, add_zero, zero_add,
      hxy, hyx, one_smul]
  · have c1 : Q * N = N := by
      have := congrArg (· * N) h1
      simpa only [add_mul, b, add_zero, one_mul] using this
    have c2 : N * Q' = N := by
      have := congrArg (N * ·) h1
      simpa only [mul_add, a, zero_add, mul_one] using this
    refine ⟨by rw [← c2, mul_assoc, ← mul_assoc Q', b, zero_mul, mul_zero], ?_⟩
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, c1, b, smul_zero, add_zero, mul_add, mul_smul_comm, mul_smul_comm,
      smul_mul_assoc, smul_mul_assoc, a, c2, smul_zero, smul_zero, zero_add, smul_smul]

theorem one_add_pow {A : Type} [Ring A] {N : A} (h : N * N = 0) (m : ℕ) : (1 + N) ^ m = 1 + m • N := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, ih, add_mul, mul_add, mul_add, smul_mul_assoc m N N, h, succ_nsmul]; simp [add_assoc, add_comm N]

end

theorem conj_pow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E), IsHermND σ JT → ∀ k : ℕ, 0 < k →
    ∃ (M : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) (t : GL (Fin nT) (AF F ⊗[F] E)),
      mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) M * dC (AF F ⊗[F] E) nT = dC (AF F ⊗[F] E) nT * t.1 ∧
      ∀ n : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT),
        mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) n * dC (AF F ⊗[F] E) nT = dC (AF F ⊗[F] E) nT →
        M * n * M⁻¹ = n ^ (k * k) := by
  intro F E _ _ _ _ _ σ n J hJ k hk
  let R := AF F ⊗[F] E
  let q : ℚ →+* R := (incAF F E).comp (algebraMap ℚ E)
  have hq : ∀ r, cAF σ (q r) = q r := fun r =>
    congrArg (incAF F E) (show σ (algebraMap ℚ E r) = algebraMap ℚ E r by simp)
  have hk' : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hxy : q k * q (k : ℚ)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hk', map_one]
  have hyx : q (k : ℚ)⁻¹ * q k = 1 := by rw [mul_comm, hxy]
  have h2 : q (1 / 2) * 2 = 1 := by rw [← map_ofNat q 2, ← map_mul]; norm_num
  let Q : Matrix (Fin (n + n)) (Fin (n + n)) R := q (1 / 2) • (dC R n * (dC R n)ᵀ)
  let Q' : Matrix (Fin (n + n)) (Fin (n + n)) R := q (1 / 2) • (aC R n * (aC R n)ᵀ)
  let J' := J.map (incAF F E)
  let D : Matrix (Fin (n + n)) (Fin (n + n)) R := (dbl J').submatrix finSumFinEquiv.symm finSumFinEquiv.symm
  have hD : JR (AF F) (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) = D := by
    ext i j
    obtain ⟨p, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨r, rfl⟩ := finSumFinEquiv.surjective j
    simp only [JR, D, J', GlobalTheory.WeilSchrodinger.DblTargetF.dblG, dbl, Matrix.map_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rcases p with p | p <;> rcases r with r | r <;> simp
  have h1 : Q + Q' = 1 := by rw [← smul_add, CC_add, smul_smul, h2, one_smul]
  have hQ : Q * Q' = 0 := by
    simp only [Q, Q', Matrix.smul_mul, Matrix.mul_smul]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (dC R n)ᵀ, C_A]; simp
  have hQ' : Q' * Q = 0 := by
    simp only [Q, Q', Matrix.smul_mul, Matrix.mul_smul]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (aC R n)ᵀ, A_C]; simp
  have hQD : Q * D * Q = 0 := by
    simp only [Q, Matrix.smul_mul, Matrix.mul_smul]
    rw [Matrix.mul_assoc (dC R n), C_D, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (aC R n)ᵀ, A_C]; simp
  have hQD' : Q' * D * Q' = 0 := by
    simp only [Q', Matrix.smul_mul, Matrix.mul_smul]
    rw [Matrix.mul_assoc (aC R n), A_D, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (dC R n)ᵀ, C_A]; simp
  have hQ'C : Q' * dC R n = 0 := by
    simp only [Q', Matrix.smul_mul]
    rw [Matrix.mul_assoc, A_C]; simp
  have hQC : Q * dC R n = dC R n := by
    have := congrArg (· * dC R n) h1
    simpa only [Matrix.add_mul, hQ'C, add_zero, Matrix.one_mul] using this
  have f1 := fun N => ring_facts (D := D) (N := N) hxy h1 hQ hQ'
  have f2 := ring_facts (D := D) (N := 0) hyx h1 hQ hQ'
  let M : GL (Fin (n + n)) R := ⟨q k • Q + q (k : ℚ)⁻¹ • Q', q (k : ℚ)⁻¹ • Q + q k • Q', (f1 0).1, f2.1⟩
  have haC : (aC R n).map (cAF σ) = aC R n := by
    ext i j
    obtain ⟨p, rfl⟩ := finSumFinEquiv.surjective i
    simp only [Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
    rcases p with p | p <;> simp [Matrix.one_apply, apply_ite (cAF σ)]
  have hsm : ∀ (r : ℚ) (X : Matrix (Fin (n + n)) (Fin (n + n)) R), (q r • X).map (cAF σ) = q r • X.map (cAF σ) :=
    fun r X => by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hq]
  have hM : (M.1.map (cAF σ))ᵀ = M.1 := by
    show ((q k • Q + q (k : ℚ)⁻¹ • Q').map (cAF σ))ᵀ = q k • Q + q (k : ℚ)⁻¹ • Q'
    rw [Matrix.map_add _ (map_add _), hsm, hsm, hsm, hsm, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
      Matrix.transpose_map, dC_map, haC]
    simp only [Q, Q', Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hmem : M ∈ HR (AF F) σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) := by
    show (M.1.map (cAF σ))ᵀ * JR (AF F) _ * M.1 = JR (AF F) _
    rw [hM, hD]
    exact (f1 0).2.1 hQD hQD'
  let t : GL (Fin n) R := ⟨q k • 1, q (k : ℚ)⁻¹ • 1, by simp only [Matrix.smul_mul, Matrix.one_mul, smul_smul, hxy, one_smul],
    by simp only [Matrix.smul_mul, Matrix.one_mul, smul_smul, hyx, one_smul]⟩
  refine ⟨(⟨M, hmem⟩ : HR (AF F) σ _), t, ?_, fun g hg => ?_⟩
  · show (q k • Q + q (k : ℚ)⁻¹ • Q') * dC R n = dC R n * (q k • 1)
    rw [Matrix.add_mul, Matrix.smul_mul _ Q, Matrix.smul_mul _ Q', hQC, hQ'C, smul_zero, add_zero, Matrix.mul_smul,
      Matrix.mul_one]
  · set G := mtF σ _ g with hG
    have hu : (G.map (cAF σ))ᵀ * JR (AF F) _ * G = JR (AF F) _ := g.2
    rw [hD] at hu
    have hJu : IsUnit J'.det := by
      have := (Ne.isUnit hJ.2).map (incAF F E)
      rwa [RingHom.map_det] at this
    have a1 : (G - 1) * Q = 0 := by
      simp only [Q, Matrix.mul_smul]
      rw [← Matrix.mul_assoc, Matrix.sub_mul, hg, Matrix.one_mul, sub_self, Matrix.zero_mul, smul_zero]
    have a2 : (aC R n)ᵀ * (G - 1) = 0 := by
      have b1 : (dC R n)ᵀ * (G.map (cAF σ))ᵀ = (dC R n)ᵀ := by
        rw [← Matrix.transpose_mul, ← dC_map (cAF σ) n, ← Matrix.map_mul, hg]
      have b2 : (dC R n)ᵀ * D * G = (dC R n)ᵀ * D := by
        conv_rhs => rw [← hu, ← Matrix.mul_assoc, ← Matrix.mul_assoc, b1]
      rw [C_D] at b2
      have b3 : J' * ((aC R n)ᵀ * (G - 1)) = 0 := by
        rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, b2, sub_self]
      rw [← Matrix.one_mul (_ * _), ← Matrix.nonsing_inv_mul _ hJu, Matrix.mul_assoc, b3, Matrix.mul_zero]
    have a3 : Q' * (G - 1) = 0 := by
      simp only [Q', Matrix.smul_mul]
      rw [Matrix.mul_assoc, a2, Matrix.mul_zero, smul_zero]
    obtain ⟨n1, n2⟩ := (f1 (G - 1)).2.2 a1 a3
    refine Subtype.ext (Units.ext ?_)
    have e : mtF σ _ (g ^ (k * k)) = G ^ (k * k) := by
      rw [hG, mtF, mtF, map_pow, Units.val_pow_eq_pow_val]
    refine Eq.trans ?_ e.symm
    show (q k • Q + q (k : ℚ)⁻¹ • Q') * G * (q (k : ℚ)⁻¹ • Q + q k • Q') = _
    rw [← add_sub_cancel 1 G, one_add_pow n1, mul_add _ 1 (G - 1), mul_one, add_mul (q k • Q + q (k : ℚ)⁻¹ • Q'),
      (f1 0).1, n2, map_natCast, ← Nat.cast_mul, Nat.cast_smul_eq_nsmul]

end PositivityTheory.ThKW.PhaseFourierInjectivity

end
