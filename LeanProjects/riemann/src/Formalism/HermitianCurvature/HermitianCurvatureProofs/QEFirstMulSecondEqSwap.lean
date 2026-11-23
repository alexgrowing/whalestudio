import Formalism.HermitianCurvature.StatementWd
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FirstEmbeddingOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositionInsertionDiagonalCompat
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondEmbedMulFirstEmbedApply

namespace Formalism.FourierDecayAlt.P.Wd4

open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.W

section Units

variable {K B : Type} [Field K] [Ring B] [Algebra K B]

def PE (e : Fin 2 → Fin 2 → B) : M2 B := Matrix.of fun i j => e j i

def QE (e : Fin 2 → Fin 2 → B) : M2 B := Matrix.of fun i j => e i j

def RhE (e : Fin 2 → Fin 2 → B) (D : K) : M2 B := (D - 1)⁻¹ • (D • (1 : M2 B) - PE e)

def RhtE (e : Fin 2 → Fin 2 → B) (d : K) : M2 B := (d - 1)⁻¹ • (d • (1 : M2 B) - QE e)

structure MU (e : Fin 2 → Fin 2 → B) : Prop where
  mul : ∀ i j k l, e i j * e k l = if j = k then e i l else 0
  sum : e 0 0 + e 1 1 = 1

theorem firstEmbed_sub (M N : M2 B) : E1 (M - N) = E1 M - E1 N := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [E1, Matrix.of_apply, Matrix.sub_apply]
  split_ifs <;> simp

theorem eval_two_sub (M N : M2 B) : E2 (M - N) = E2 M - E2 N := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [E2, Matrix.of_apply, Matrix.sub_apply]
  split_ifs <;> simp

theorem kronecker_E1_smul (c : K) (M : M2 B) : E1 (c • M) = c • E1 M := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [E1, Matrix.of_apply, Matrix.smul_apply]
  split_ifs <;> simp

theorem eval_two_smul (c : K) (M : M2 B) : E2 (c • M) = c • E2 M := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [E2, Matrix.of_apply, Matrix.smul_apply]
  split_ifs <;> simp

theorem swap_mul_firstEmbed (M : M2 B) : Pf B * E1 M = E2 M * Pf B := by
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [E1, E2, Pf, Matrix.mul_apply, Fintype.sum_prod_type]

theorem swap_mul_secondEmbed (M : M2 B) : Pf B * E2 M = E1 M * Pf B := by
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [E1, E2, Pf, Matrix.mul_apply, Fintype.sum_prod_type]

variable {e : Fin 2 → Fin 2 → B}

theorem PE_first_mul_second_eq_swap (he : MU e) : E1 (PE e) * E2 (PE e) = Pf B * E1 (PE e) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [E1, E2, Pf, PE, Matrix.mul_apply, Fintype.sum_prod_type, he.mul]

theorem PE_second_mul_first_eq_swap (he : MU e) : E2 (PE e) * E1 (PE e) = Pf B * E2 (PE e) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [E1, E2, Pf, PE, Matrix.mul_apply, Fintype.sum_prod_type, he.mul]

theorem QE_first_mul_second_eq_swap (he : MU e) : E1 (QE e) * E2 (QE e) = E1 (QE e) * Pf B := by
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [E1, E2, Pf, QE, Matrix.mul_apply, Fintype.sum_prod_type, he.mul]

theorem QE_second_mul_first_eq_swap (he : MU e) : E2 (QE e) * E1 (QE e) = E2 (QE e) * Pf B := by
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [E1, E2, Pf, QE, Matrix.mul_apply, Fintype.sum_prod_type, he.mul]

theorem ybe_alg {C : Type} [Ring C] [Algebra K C] (p12 p13 p23 : C) (u v : K)
    (h1 : p13 * p23 = p12 * p13) (h2 : p23 * p12 = p12 * p13)
    (h3 : p23 * p13 = p12 * p23) (h4 : p13 * p12 = p12 * p23) :
    ((u - v) • (1 : C) - p12) * (u • (1 : C) - p13) * (v • (1 : C) - p23) =
      (v • (1 : C) - p23) * (u • (1 : C) - p13) * ((u - v) • (1 : C) - p12) := by
  have tri : p12 * p13 * p23 = p12 * p23 * p12 := by
    calc p12 * p13 * p23 = p23 * p12 * p23 := by rw [h2]
      _ = p23 * (p13 * p12) := by rw [mul_assoc, h4]
      _ = p12 * p23 * p12 := by rw [← mul_assoc, h3]
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_sub,
    h1, h2, h3, h4, tri]
  module

theorem ybet_alg {C : Type} [Ring C] [Algebra K C] (p12 q13 q23 : C) (d' d : K)
    (g1 : p12 * q13 = q23 * p12) (g2 : p12 * q23 = q13 * p12)
    (g3 : q13 * q23 = q13 * p12) (g4 : q23 * q13 = q23 * p12) :
    ((d - d') • (1 : C) - p12) * (d' • (1 : C) - q13) * (d • (1 : C) - q23) =
      (d • (1 : C) - q23) * (d' • (1 : C) - q13) * ((d - d') • (1 : C) - p12) := by
  have tri : q23 * p12 * q23 = q23 * p12 * p12 := by
    rw [mul_assoc, g2, ← mul_assoc, g4]
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_sub,
    g1, g2, g3, g4, tri]
  module

theorem rtt_PE (he : MU e) (u v : K) :
    ((u - v) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) - Pf B) * E1 (u • (1 : M2 B) - PE e) *
        E2 (v • (1 : M2 B) - PE e) =
      E2 (v • (1 : M2 B) - PE e) * E1 (u • (1 : M2 B) - PE e) *
        ((u - v) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) - Pf B) := by
  rw [firstEmbed_sub, kronecker_E1_smul, first_embedding_one, eval_two_sub, eval_two_smul, entries_mem_one]
  exact ybe_alg _ _ _ u v (PE_first_mul_second_eq_swap he) (swap_mul_firstEmbed _).symm (PE_second_mul_first_eq_swap he) (swap_mul_secondEmbed _).symm

theorem rtt_QE (he : MU e) (d' d : K) :
    ((d - d') • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) - Pf B) * E1 (d' • (1 : M2 B) - QE e) *
        E2 (d • (1 : M2 B) - QE e) =
      E2 (d • (1 : M2 B) - QE e) * E1 (d' • (1 : M2 B) - QE e) *
        ((d - d') • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) - Pf B) := by
  rw [firstEmbed_sub, kronecker_E1_smul, first_embedding_one, eval_two_sub, eval_two_smul, entries_mem_one]
  exact ybet_alg _ _ _ d' d (swap_mul_firstEmbed _) (swap_mul_secondEmbed _) (QE_first_mul_second_eq_swap he) (QE_second_mul_first_eq_swap he)

theorem J_PE (he : MU e) : YangianSpanCharacter.T.J B * PE e = YangianSpanCharacter.T.J B - QE e * YangianSpanCharacter.T.J B := by
  have h := he.sum
  have h' : e 1 1 = 1 - e 0 0 := eq_sub_of_add_eq' h
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [YangianSpanCharacter.T.J, PE, QE, Matrix.mul_apply, Fin.sum_univ_two, h'] <;> first | rfl | abel)

theorem J_QE (he : MU e) : YangianSpanCharacter.T.J B * QE e = YangianSpanCharacter.T.J B - PE e * YangianSpanCharacter.T.J B := by
  have h := he.sum
  have h' : e 1 1 = 1 - e 0 0 := eq_sub_of_add_eq' h
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [YangianSpanCharacter.T.J, PE, QE, Matrix.mul_apply, Fin.sum_univ_two, h'] <;> first | rfl | abel)

theorem QE_J_PE (he : MU e) : QE e * YangianSpanCharacter.T.J B * PE e = -(QE e * YangianSpanCharacter.T.J B) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [YangianSpanCharacter.T.J, PE, QE, Matrix.mul_apply, Fin.sum_univ_two, he.mul]

theorem PE_J_QE (he : MU e) : PE e * YangianSpanCharacter.T.J B * QE e = -(YangianSpanCharacter.T.J B * QE e) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [YangianSpanCharacter.T.J, PE, QE, Matrix.mul_apply, Fin.sum_univ_two, he.mul]; rfl)

theorem det1 (he : MU e) (D : K) :
    ((D + 1) • (1 : M2 B) - QE e) * YangianSpanCharacter.T.J B * (D • (1 : M2 B) - PE e) =
      ((D + 1) * (D - 1)) • YangianSpanCharacter.T.J B := by
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_sub,
    QE_J_PE he, J_PE he]
  module

theorem det2 (he : MU e) (D : K) :
    (D • (1 : M2 B) - PE e) * YangianSpanCharacter.T.J B * ((D + 1) • (1 : M2 B) - QE e) =
      ((D + 1) * (D - 1)) • YangianSpanCharacter.T.J B := by
  simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_sub,
    PE_J_QE he, J_QE he]
  module

theorem RhE_transpose (D : K) : (RhE e D)ᵀ = (D - 1)⁻¹ • (D • (1 : M2 B) - QE e) := by
  unfold RhE
  rw [Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one]
  rfl

theorem RhtE_transpose (d : K) : (RhtE e d)ᵀ = (d - 1)⁻¹ • (d • (1 : M2 B) - PE e) := by
  unfold RhtE
  rw [Matrix.transpose_smul, Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one]
  rfl

theorem det_RhE (he : MU e) (D : K) (h0 : D ≠ 0) (h1 : D ≠ 1) :
    (RhE e (D + 1))ᵀ * YangianSpanCharacter.T.J B * RhE e D = ((D + 1) / D) • YangianSpanCharacter.T.J B ∧
      RhE e D * YangianSpanCharacter.T.J B * (RhE e (D + 1))ᵀ = ((D + 1) / D) • YangianSpanCharacter.T.J B := by
  have h1' : D - 1 ≠ 0 := sub_ne_zero.2 h1
  have hs : (D + 1 - 1)⁻¹ * (D - 1)⁻¹ * ((D + 1) * (D - 1)) = (D + 1) / D := by
    rw [add_sub_cancel_right]; field_simp
  have hs' : (D - 1)⁻¹ * (D + 1 - 1)⁻¹ * ((D + 1) * (D - 1)) = (D + 1) / D := by
    rw [add_sub_cancel_right]; field_simp
  rw [RhE_transpose]
  unfold RhE
  constructor
  · rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, det1 he D, smul_smul, smul_smul, hs]
  · rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, det2 he D, smul_smul, smul_smul, hs']

theorem det_RhtE (he : MU e) (d : K) (h1 : d ≠ 1) (h2 : d - 1 ≠ 1) :
    (RhtE e (d - 1))ᵀ * YangianSpanCharacter.T.J B * RhtE e d = (d / (d - 1)) • YangianSpanCharacter.T.J B ∧
      RhtE e d * YangianSpanCharacter.T.J B * (RhtE e (d - 1))ᵀ = (d / (d - 1)) • YangianSpanCharacter.T.J B := by
  have h1' : d - 1 ≠ 0 := sub_ne_zero.2 h1
  have h2' : d - 1 - 1 ≠ 0 := sub_ne_zero.2 h2
  have hs : (d - 1 - 1)⁻¹ * (d - 1)⁻¹ * ((d - 1 + 1) * (d - 1 - 1)) = d / (d - 1) := by
    rw [sub_add_cancel]; field_simp
  have hs' : (d - 1)⁻¹ * (d - 1 - 1)⁻¹ * ((d - 1 + 1) * (d - 1 - 1)) = d / (d - 1) := by
    rw [sub_add_cancel]; field_simp
  have e1 := det1 he (d - 1)
  have e2 := det2 he (d - 1)
  rw [sub_add_cancel] at e1 e2
  rw [sub_add_cancel] at hs hs'
  rw [RhtE_transpose]
  unfold RhtE
  constructor
  · rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, e2, smul_smul, smul_smul, hs]
  · rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, e1, smul_smul, smul_smul, hs']

theorem comm_one (b : B) (i j : Fin 2) : Commute ((1 : M2 B) i j) b := by
  rw [Matrix.one_apply]
  split_ifs
  · exact Commute.one_left _
  · exact Commute.zero_left _

theorem comm_RhE (D : K) (b : B) (hb : ∀ i j, Commute (e i j) b) (i j : Fin 2) :
    Commute (RhE e D i j) b := by
  unfold RhE
  rw [Matrix.smul_apply, Matrix.sub_apply, Matrix.smul_apply]
  exact (((comm_one b i j).smul_left D).sub_left (hb j i)).smul_left _

theorem comm_RhtE (d : K) (b : B) (hb : ∀ i j, Commute (e i j) b) (i j : Fin 2) :
    Commute (RhtE e d i j) b := by
  unfold RhtE
  rw [Matrix.smul_apply, Matrix.sub_apply, Matrix.smul_apply]
  exact (((comm_one b i j).smul_left d).sub_left (hb i j)).smul_left _

theorem rtt_RhE (he : MU e) (Ya Y Y' : K) : RTTat (fun Y => RhE e (Y - Ya)) Y Y' := by
  have h := rtt_PE he (Y' - Ya) (Y - Ya)
  rw [sub_sub_sub_cancel_right] at h
  unfold RTTat RhE
  simp only [kronecker_E1_smul, eval_two_smul, mul_smul_comm, smul_mul_assoc]
  rw [h, smul_comm]

theorem rtt_RhtE (he : MU e) (Yb Y Y' : K) : RTTat (fun Y => RhtE e (Yb - Y)) Y Y' := by
  have h := rtt_QE he (Yb - Y') (Yb - Y)
  rw [sub_sub_sub_cancel_left] at h
  unfold RTTat RhtE
  simp only [kronecker_E1_smul, eval_two_smul, mul_smul_comm, smul_mul_assoc]
  rw [h, smul_comm]

theorem rtt_mul_at (M N : K → M2 B) (Y Y' : K) (hM : RTTat M Y Y') (hN : RTTat N Y Y')
    (hc : ∀ Y Y' i j k l, Commute (M Y i j) (N Y' k l)) : RTTat (fun Y => M Y * N Y) Y Y' := by
  unfold RTTat at hM hN ⊢
  set Rm := (Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) - Pf B with hRm
  have c1 : E1 (N Y') * E2 (M Y) = E2 (M Y) * E1 (N Y') :=
    first_second_embedding_commute _ _ fun i j k l => ((hc Y Y' k l i j).eq).symm
  have c2 : E1 (M Y') * E2 (N Y) = E2 (N Y) * E1 (M Y') :=
    first_second_embedding_commute _ _ fun i j k l => (hc Y' Y i j k l).eq
  show Rm * E1 (M Y' * N Y') * E2 (M Y * N Y) = E2 (M Y * N Y) * E1 (M Y' * N Y') * Rm
  rw [first_embedding_mul, entries_mem_mul]
  calc Rm * (E1 (M Y') * E1 (N Y')) * (E2 (M Y) * E2 (N Y))
      = Rm * E1 (M Y') * (E1 (N Y') * E2 (M Y)) * E2 (N Y) := by simp only [mul_assoc]
    _ = Rm * E1 (M Y') * (E2 (M Y) * E1 (N Y')) * E2 (N Y) := by rw [c1]
    _ = (Rm * E1 (M Y') * E2 (M Y)) * E1 (N Y') * E2 (N Y) := by simp only [mul_assoc]
    _ = E2 (M Y) * E1 (M Y') * (Rm * E1 (N Y') * E2 (N Y)) := by rw [hM]; simp only [mul_assoc]
    _ = E2 (M Y) * E1 (M Y') * (E2 (N Y) * E1 (N Y') * Rm) := by rw [hN]
    _ = E2 (M Y) * (E1 (M Y') * E2 (N Y)) * E1 (N Y') * Rm := by simp only [mul_assoc]
    _ = E2 (M Y) * (E2 (N Y) * E1 (M Y')) * E1 (N Y') * Rm := by rw [c2]
    _ = (E2 (M Y) * E2 (N Y)) * (E1 (M Y') * E1 (N Y')) * Rm := by simp only [mul_assoc]

theorem detAt_iff (M : K → M2 B) (q : K → K) (Y : K) :
    DetAt M q Y ↔ (M (Y + 1))ᵀ * YangianSpanCharacter.T.J B * M Y = q Y • YangianSpanCharacter.T.J B ∧
      M Y * YangianSpanCharacter.T.J B * (M (Y + 1))ᵀ = q Y • YangianSpanCharacter.T.J B := by
  simp only [DetAt, algebraMap_smul]

theorem det_mul_at (M N : K → M2 B) (q qN : K → K) (Y : K) (hM : DetAt M q Y) (hN : DetAt N qN Y)
    (hc : ∀ Y Y' i j k l, Commute (M Y i j) (N Y' k l)) :
    DetAt (fun Y => M Y * N Y) (fun Y => q Y * qN Y) Y := by
  rw [detAt_iff] at hM hN ⊢
  obtain ⟨hM1, hM2⟩ := hM
  obtain ⟨hN1, hN2⟩ := hN
  have ht : (M (Y + 1) * N (Y + 1))ᵀ = (N (Y + 1))ᵀ * (M (Y + 1))ᵀ :=
    transpose_mul_of_comm _ _ fun i j k l => (hc (Y + 1) (Y + 1) i j k l).eq
  refine ⟨?_, ?_⟩
  · show (M (Y + 1) * N (Y + 1))ᵀ * YangianSpanCharacter.T.J B * (M Y * N Y) = (q Y * qN Y) • YangianSpanCharacter.T.J B
    rw [ht]
    calc (N (Y + 1))ᵀ * (M (Y + 1))ᵀ * YangianSpanCharacter.T.J B * (M Y * N Y)
        = (N (Y + 1))ᵀ * ((M (Y + 1))ᵀ * YangianSpanCharacter.T.J B * M Y) * N Y := by simp only [mul_assoc]
      _ = (N (Y + 1))ᵀ * (q Y • YangianSpanCharacter.T.J B) * N Y := by rw [hM1]
      _ = q Y • ((N (Y + 1))ᵀ * YangianSpanCharacter.T.J B * N Y) := by rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = (q Y * qN Y) • YangianSpanCharacter.T.J B := by rw [hN1, smul_smul]
  · show M Y * N Y * YangianSpanCharacter.T.J B * (M (Y + 1) * N (Y + 1))ᵀ = (q Y * qN Y) • YangianSpanCharacter.T.J B
    rw [ht]
    calc M Y * N Y * YangianSpanCharacter.T.J B * ((N (Y + 1))ᵀ * (M (Y + 1))ᵀ)
        = M Y * (N Y * YangianSpanCharacter.T.J B * (N (Y + 1))ᵀ) * (M (Y + 1))ᵀ := by simp only [mul_assoc]
      _ = M Y * (qN Y • YangianSpanCharacter.T.J B) * (M (Y + 1))ᵀ := by rw [hN2]
      _ = qN Y • (M Y * YangianSpanCharacter.T.J B * (M (Y + 1))ᵀ) := by rw [Matrix.mul_smul, Matrix.smul_mul]
      _ = (q Y * qN Y) • YangianSpanCharacter.T.J B := by rw [hM2, smul_smul, mul_comm]

theorem detAt_RhE (he : MU e) (Ya Y : K) (h1 : Y - Ya ≠ 1) (h2 : Y + 1 - Ya ≠ 1) :
    DetAt (fun Y => RhE e (Y - Ya)) (fun Y => (Y - Ya + 1) / (Y - Ya)) Y := by
  rw [detAt_iff]
  have h0 : Y - Ya ≠ 0 := by
    intro h; apply h2; rw [add_sub_right_comm, h, zero_add]
  have hE : Y + 1 - Ya = Y - Ya + 1 := by ring
  show (RhE e (Y + 1 - Ya))ᵀ * YangianSpanCharacter.T.J B * RhE e (Y - Ya) = ((Y - Ya + 1) / (Y - Ya)) • YangianSpanCharacter.T.J B ∧
    RhE e (Y - Ya) * YangianSpanCharacter.T.J B * (RhE e (Y + 1 - Ya))ᵀ = ((Y - Ya + 1) / (Y - Ya)) • YangianSpanCharacter.T.J B
  rw [hE]
  exact det_RhE he (Y - Ya) h0 h1

theorem detAt_RhtE (he : MU e) (Yb Y : K) (h1 : Yb - Y ≠ 1) (h2 : Yb - (Y + 1) ≠ 1) :
    DetAt (fun Y => RhtE e (Yb - Y)) (fun Y => (Yb - Y) / (Yb - Y - 1)) Y := by
  rw [detAt_iff]
  have hE : Yb - (Y + 1) = Yb - Y - 1 := by ring
  show (RhtE e (Yb - (Y + 1)))ᵀ * YangianSpanCharacter.T.J B * RhtE e (Yb - Y) =
      ((Yb - Y) / (Yb - Y - 1)) • YangianSpanCharacter.T.J B ∧
    RhtE e (Yb - Y) * YangianSpanCharacter.T.J B * (RhtE e (Yb - (Y + 1)))ᵀ = ((Yb - Y) / (Yb - Y - 1)) • YangianSpanCharacter.T.J B
  rw [hE] at h2 ⊢
  exact det_RhtE he (Yb - Y) h1 h2

theorem comm_diag (X : M2 B) (b : B) (h : ∀ i j, Commute (X i j) b) :
    X * Matrix.diagonal (fun _ => b) = Matrix.diagonal (fun _ => b) * X := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact (h i j).eq

end Units

section Star

variable {K B : Type} [Field K] [StarRing K] [Ring B] [StarRing B] [Algebra K B] [StarModule K B]
  {e : Fin 2 → Fin 2 → B}

theorem RhE_herm (hs : ∀ i j, star (e i j) = e j i) (D : K) (hD : star D = D) :
    (RhE e D)ᴴ = RhE e D := by
  have hP : (PE e)ᴴ = PE e := by
    ext i j
    simp [PE, hs]
  unfold RhE
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, star_inv₀, star_sub, star_one, hD, hP]

theorem RhtE_herm (hs : ∀ i j, star (e i j) = e j i) (d : K) (hd : star d = d) :
    (RhtE e d)ᴴ = RhtE e d := by
  have hQ : (QE e)ᴴ = QE e := by
    ext i j
    simp [QE, hs]
  unfold RhtE
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, star_inv₀, star_sub, star_one, hd, hQ]

theorem herm_plus (G Ta T0 Rh : M2 B) (hG : Gᴴ = G) (hGTa : (G * Ta)ᴴ = G * Ta)
    (hGT0 : (G * T0)ᴴ = G * T0) (hRh : Rhᴴ = Rh) (hc : Rh * G = G * Rh)
    (hex : Ta * T0 * Rh = Rh * T0 * Ta) : (G * Ta * (T0 * Rh))ᴴ = G * Ta * (T0 * Rh) := by
  calc (G * Ta * (T0 * Rh))ᴴ = Rhᴴ * T0ᴴ * (G * Ta)ᴴ := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul T0 Rh]
    _ = Rh * (T0ᴴ * Gᴴ) * Ta := by rw [hRh, hGTa, hG]; simp only [mul_assoc]
    _ = Rh * (G * T0) * Ta := by rw [← Matrix.conjTranspose_mul, hGT0]
    _ = G * (Rh * T0 * Ta) := by rw [← mul_assoc, hc]; simp only [mul_assoc]
    _ = G * Ta * (T0 * Rh) := by rw [← hex]; simp only [mul_assoc]

theorem herm_minus (G Tb T0 Rh : M2 B) (hG : Gᴴ = G) (hGTb : (G * Tb)ᴴ = G * Tb)
    (hGT0 : (G * T0)ᴴ = G * T0) (hRh : Rhᴴ = Rh) (hc : Rh * G = G * Rh)
    (hex : Tb * Rh * T0 = T0 * Rh * Tb) : (G * Tb * (Rh * T0))ᴴ = G * Tb * (Rh * T0) := by
  calc (G * Tb * (Rh * T0))ᴴ = T0ᴴ * Rhᴴ * (G * Tb)ᴴ := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul Rh T0]
    _ = T0ᴴ * (Rh * G) * Tb := by rw [hRh, hGTb]; simp only [mul_assoc]
    _ = (T0ᴴ * Gᴴ) * Rh * Tb := by rw [hc, hG]; simp only [mul_assoc]
    _ = G * (T0 * Rh * Tb) := by rw [← Matrix.conjTranspose_mul, hGT0]; simp only [mul_assoc]
    _ = G * Tb * (Rh * T0) := by rw [← hex]; simp only [mul_assoc]

end Star

section Slots

variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]

theorem eU_MU (a : S) : MU (eU a : Fin 2 → Fin 2 → SlopeTestRemainingChoices S A) where
  mul := Wd1.eU_mul_eU a
  sum := by
    have h := Wd1.sum_eU_diag (A := A) a
    rwa [Fin.sum_univ_two] at h

theorem freeOf_diagScalar {a : S} {b : SlopeTestRemainingChoices S A} (hb : FreeOf a b) : FreeOf2 a (d0 b) := by
  intro i j
  unfold d0
  rw [Matrix.diagonal_apply]
  split_ifs
  · exact hb
  · exact fun _ _ => Commute.zero_right _

theorem freeOf2_mul {a : S} {M N : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 a M) (hN : FreeOf2 a N) :
    FreeOf2 a (M * N) := by
  intro i j k l
  rw [Matrix.mul_apply]
  exact Commute.sum_right _ _ _ fun m _ => (hM i m k l).mul_right (hN m j k l)

theorem diagScalar_mul (b c : SlopeTestRemainingChoices S A) : d0 (b * c) = d0 b * d0 c := by
  unfold d0
  rw [Matrix.diagonal_mul_diagonal]

theorem diagScalar_conjTranspose (b : SlopeTestRemainingChoices S A) : (d0 b)ᴴ = d0 (star b) := by
  unfold d0
  rw [Matrix.diagonal_conjTranspose]
  rfl

theorem form_herm {a : S} {RR : SlopeTestRemainingChoices S A} {T : M2 (SlopeTestRemainingChoices S A)} (hRR : FreeOf a RR) (hT : FreeOf2 a T)
    (h : (d0 RR * T)ᴴ = d0 RR * T) : star (RR * ins a T) = RR * ins a T := by
  have h1 : RR * ins a T = ins a (d0 RR * T) := by
    rw [Wd1.ins_mul a _ _ (freeOf_diagScalar hRR), Wd1.insert_diagonal_extract]
  rw [h1, Wd1.ins_star a _ (freeOf2_mul (freeOf_diagScalar hRR) hT), h]

theorem herm_transpose {RR : SlopeTestRemainingChoices S A} {T : M2 (SlopeTestRemainingChoices S A)} (h : (d0 RR * T)ᴴ = d0 RR * T) :
    (d0 RR * Tᵀ)ᴴ = d0 RR * Tᵀ := by
  ext1 i j
  have h' := congrFun (congrFun h j) i
  unfold d0 at h' ⊢
  rw [Matrix.conjTranspose_apply, Matrix.diagonal_mul] at h' ⊢
  rw [Matrix.diagonal_mul] at h' ⊢
  exact h'

end Slots

end Formalism.FourierDecayAlt.P.Wd4

namespace Formalism.FourierDecayAlt.P

open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd

theorem letter_module_plus : Formalism.FourierDecayAlt.Wd.LetterPlus := by
  intro K A S _ _ _ _ _ _ _ _ Ω RR TT q a Ya hM hRR hTT hYa hsYa
  have he : Wd4.MU (eU a : Fin 2 → Fin 2 → SlopeTestRemainingChoices S A) := Wd4.eU_MU a
  have hform : star (RR * ins a (TT Ya)) = RR * ins a (TT Ya) :=
    Wd4.form_herm hRR (hTT Ya) (hM.herm Ya hYa hsYa)
  have hc : ∀ Y Y' i j k l, Commute (TT Y i j) (Wd4.RhE (eU a) (Y' - Ya) k l) :=
    fun Y Y' i j k l => (Wd4.comm_RhE (Y' - Ya) (TT Y i j) (fun r s => hTT Y i j r s) k l).symm
  refine ⟨hform, ?_, ?_, ?_, ?_⟩
  · rintro Y ⟨hY, -⟩ hsY
    show (d0 (RR * ins a (TT Ya)) * (TT Y * Rh0 a (Y - Ya)))ᴴ =
      d0 (RR * ins a (TT Ya)) * (TT Y * Rh0 a (Y - Ya))
    rw [Wd4.diagScalar_mul]
    refine Wd4.herm_plus _ _ _ _ ?_ ?_ (hM.herm Y hY hsY) ?_ ?_ ?_
    · rw [Wd4.diagScalar_conjTranspose, hM.form_herm]
    · rw [← Wd4.diagScalar_mul, Wd4.diagScalar_conjTranspose, hform]
    · exact Wd4.RhE_herm (Wd1.star_eU a) (Y - Ya) (by rw [star_sub, hsY, hsYa])
    · exact Wd4.comm_diag _ RR (Wd4.comm_RhE (Y - Ya) RR hRR)
    · exact exchange_relation_plus K A S Ω RR TT q a Y Ya hM hTT hY hYa
  · rintro Y ⟨hY, -⟩ Y' ⟨hY', -⟩
    exact Wd4.rtt_mul_at TT (fun Y => Wd4.RhE (eU a) (Y - Ya)) Y Y' (hM.rtt Y hY Y' hY')
      (Wd4.rtt_RhE he Ya Y Y') hc
  · rintro Y ⟨hY, hY1⟩ ⟨hY', hY1'⟩
    exact Wd4.det_mul_at TT (fun Y => Wd4.RhE (eU a) (Y - Ya)) q _ Y (hM.det Y hY hY')
      (Wd4.detAt_RhE he Ya Y hY1 hY1') hc
  · intro Y hsY
    simp only [star_mul', star_div₀, star_add, star_sub, star_one, hsY, hsYa, hM.q_real Y hsY]

theorem letter_module_minus : Formalism.FourierDecayAlt.Wd.LetterMinus := by
  intro K A S _ _ _ _ _ _ _ _ Ω RR TT q b Yb hM hRR hTT hYb hsYb
  have he : Wd4.MU (eU b : Fin 2 → Fin 2 → SlopeTestRemainingChoices S A) := Wd4.eU_MU b
  have hform : star (RR * ins b (TT Yb)ᵀ) = RR * ins b (TT Yb)ᵀ :=
    Wd4.form_herm hRR (fun i j => hTT Yb j i) (Wd4.herm_transpose (hM.herm Yb hYb hsYb))
  have hc : ∀ Y Y' i j k l, Commute (Wd4.RhtE (eU b) (Yb - Y) i j) (TT Y' k l) :=
    fun Y Y' i j k l => Wd4.comm_RhtE (Yb - Y) (TT Y' k l) (fun r s => hTT Y' k l r s) i j
  refine ⟨hform, ?_, ?_, ?_, ?_⟩
  · rintro Y ⟨hY, -⟩ hsY
    show (d0 (RR * ins b (TT Yb)ᵀ) * (Rht0 b (Yb - Y) * TT Y))ᴴ =
      d0 (RR * ins b (TT Yb)ᵀ) * (Rht0 b (Yb - Y) * TT Y)
    rw [Wd4.diagScalar_mul]
    refine Wd4.herm_minus _ _ _ _ ?_ ?_ (hM.herm Y hY hsY) ?_ ?_ ?_
    · rw [Wd4.diagScalar_conjTranspose, hM.form_herm]
    · rw [← Wd4.diagScalar_mul, Wd4.diagScalar_conjTranspose, hform]
    · exact Wd4.RhtE_herm (Wd1.star_eU b) (Yb - Y) (by rw [star_sub, hsY, hsYb])
    · exact Wd4.comm_diag _ RR (Wd4.comm_RhtE (Yb - Y) RR hRR)
    · exact exchange_relation_minus K A S Ω RR TT q b Y Yb hM hTT hY hYb
  · rintro Y ⟨hY, -⟩ Y' ⟨hY', -⟩
    exact Wd4.rtt_mul_at (fun Y => Wd4.RhtE (eU b) (Yb - Y)) TT Y Y' (Wd4.rtt_RhtE he Yb Y Y')
      (hM.rtt Y hY Y' hY') hc
  · rintro Y ⟨hY, hY1⟩ ⟨hY', hY1'⟩
    have h := Wd4.det_mul_at (fun Y => Wd4.RhtE (eU b) (Yb - Y)) TT _ q Y
      (Wd4.detAt_RhtE he Yb Y hY1 hY1') (hM.det Y hY hY') hc
    simp only [mul_comm _ (q _)] at h
    exact h
  · intro Y hsY
    simp only [star_mul', star_div₀, star_sub, star_one, hsY, hsYb, hM.q_real Y hsY]

end Formalism.FourierDecayAlt.P
