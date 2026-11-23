import Formalism.HermitianCurvature.StatementWd
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PositionInsertionDiagonalCompat
import Formalism.YangianSpanCharacter.YangianRelationFirst

namespace Formalism.FourierDecayAlt.P.Wd11

open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.Wd1

section Basic

variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]

theorem io_mul (x y : A) : (io (x * y) : SlopeTestRemainingChoices S A) = io x * io y := by
  unfold io; exact map_mul _ x y

theorem io_one : (io (1 : A) : SlopeTestRemainingChoices S A) = 1 := by
  unfold io; exact map_one _

theorem io_zero : (io (0 : A) : SlopeTestRemainingChoices S A) = 0 := by
  unfold io; exact map_zero _

theorem io_neg (x : A) : (io (-x) : SlopeTestRemainingChoices S A) = -io x := by
  unfold io; exact map_neg _ x

theorem io_star [StarRing A] (x : A) : star (io x : SlopeTestRemainingChoices S A) = io (star x) := by
  unfold io
  rw [Matrix.star_eq_conjTranspose, Matrix.scalar_apply, Matrix.scalar_apply,
    Matrix.diagonal_conjTranspose]
  rfl

theorem eU_io (a : S) (i j : Fin 2) (x : A) : Commute (eU a i j : SlopeTestRemainingChoices S A) (io x) := by
  show eU a i j * io x = io x * eU a i j
  ext u v
  unfold io
  rw [Matrix.scalar_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, eU_apply]
  split_ifs <;> simp

theorem free_io (a : S) (x : A) : FreeOf a (io x : SlopeTestRemainingChoices S A) := fun i j => eU_io a i j x

theorem free_one (a : S) : FreeOf a (1 : SlopeTestRemainingChoices S A) := fun _ _ => Commute.one_right _

theorem free_zero (a : S) : FreeOf a (0 : SlopeTestRemainingChoices S A) := fun _ _ => Commute.zero_right _

theorem free_mul {a : S} {x y : SlopeTestRemainingChoices S A} (hx : FreeOf a x) (hy : FreeOf a y) :
    FreeOf a (x * y) := fun i j => (hx i j).mul_right (hy i j)

theorem freeOf2_lift (a : S) (M : M2 A) : FreeOf2 a (lift0 M : M2 (SlopeTestRemainingChoices S A)) :=
  fun i j => free_io a (M i j)

theorem freeOf2_mul {a : S} {M N : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 a M) (hN : FreeOf2 a N) :
    FreeOf2 a (M * N) := by
  intro i j k l
  rw [Matrix.mul_apply]
  exact Commute.sum_right _ _ _ fun m _ => (hM i m k l).mul_right (hN m j k l)

theorem freeOf2_transpose {a : S} {M : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 a M) : FreeOf2 a Mᵀ :=
  fun i j => hM j i

theorem diagScalar_mul (x y : SlopeTestRemainingChoices S A) : d0 (x * y) = d0 x * d0 y := by
  unfold d0; rw [Matrix.diagonal_mul_diagonal]

theorem d0_one : d0 (1 : SlopeTestRemainingChoices S A) = 1 := by
  unfold d0; exact Matrix.diagonal_one

theorem diagScalar_mul_apply (x : SlopeTestRemainingChoices S A) (M : M2 (SlopeTestRemainingChoices S A)) (i j : Fin 2) :
    (d0 x * M) i j = x * M i j := by
  unfold d0; rw [Matrix.diagonal_mul]

theorem mul_diagScalar_apply (x : SlopeTestRemainingChoices S A) (M : M2 (SlopeTestRemainingChoices S A)) (i j : Fin 2) :
    (M * d0 x) i j = M i j * x := by
  unfold d0; rw [Matrix.mul_diagonal]

theorem diagScalar_commute_of_entries {x : SlopeTestRemainingChoices S A} {M : M2 (SlopeTestRemainingChoices S A)} (h : ∀ i j, Commute x (M i j)) :
    Commute (d0 x) M := by
  show d0 x * M = M * d0 x
  ext i j
  rw [diagScalar_mul_apply, mul_diagScalar_apply]
  exact congrFun (congrFun (h i j).eq _) _

theorem diagScalar_commute_diagScalar {x y : SlopeTestRemainingChoices S A} (h : Commute x y) : Commute (d0 x) (d0 y) := by
  show d0 x * d0 y = d0 y * d0 x
  rw [← diagScalar_mul, ← diagScalar_mul, h.eq]

theorem lift_reduction_mul (M N : M2 A) : (lift0 (M * N) : M2 (SlopeTestRemainingChoices S A)) = lift0 M * lift0 N := by
  show (M * N).map (Matrix.scalar (Ix S)) =
    M.map (Matrix.scalar (Ix S)) * N.map (Matrix.scalar (Ix S))
  exact Matrix.map_mul

theorem liftMatrix_one : (lift0 (1 : M2 A) : M2 (SlopeTestRemainingChoices S A)) = 1 := by
  show (1 : M2 A).map (Matrix.scalar (Ix S)) = 1
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem liftMatrix_diagonal_eq_diagScalar (f : A) : (lift0 (Matrix.diagonal fun _ => f) : M2 (SlopeTestRemainingChoices S A)) = d0 (io f) := by
  show (Matrix.diagonal fun _ => f).map (Matrix.scalar (Ix S)) = _
  rw [Matrix.diagonal_map (map_zero _)]
  rfl

theorem liftMatrix_conjTranspose [StarRing A] (M : M2 A) :
    (lift0 Mᴴ : M2 (SlopeTestRemainingChoices S A)) = (lift0 M)ᴴ := by
  ext1 i j
  show io (star (M j i)) = star (io (M j i))
  rw [io_star]

theorem insL_mul (a : S) (M N : M2 A) :
    (ins a (lift0 (M * N)) : SlopeTestRemainingChoices S A) = ins a (lift0 M) * ins a (lift0 N) := by
  rw [lift_reduction_mul, ins_mul a _ _ (freeOf2_lift a M)]

theorem insL_one (a : S) : (ins a (lift0 (1 : M2 A)) : SlopeTestRemainingChoices S A) = 1 := by
  rw [liftMatrix_one, ins_one]

theorem insL_diag (a : S) (f : A) :
    (ins a (lift0 (Matrix.diagonal fun _ => f)) : SlopeTestRemainingChoices S A) = io f := by
  rw [liftMatrix_diagonal_eq_diagScalar, insert_diagonal_extract]

theorem insL_star [StarRing A] (a : S) (M : M2 A) :
    star (ins a (lift0 M) : SlopeTestRemainingChoices S A) = ins a (lift0 Mᴴ) := by
  rw [ins_star a _ (freeOf2_lift a M), liftMatrix_conjTranspose]

theorem free_insL {a c : S} (h : c ≠ a) (M : M2 A) : FreeOf c (ins a (lift0 M) : SlopeTestRemainingChoices S A) :=
  ins_free h _ (freeOf2_lift c M)

def Cen (N : M2 A) : Prop := ∀ i j (x : A), Commute (N i j) x

theorem io_cen {x : A} (h : ∀ y, Commute x y) (b : SlopeTestRemainingChoices S A) : Commute (io x) b :=
  Matrix.scalar_commute x h b

theorem comm_insL {a : S} {N : M2 A} (hN : Cen N) {b : SlopeTestRemainingChoices S A} (hb : FreeOf a b) :
    Commute b (ins a (lift0 N)) :=
  ins_comm a _ b hb fun i j => (io_cen (hN i j) b).symm

theorem diagScalar_commute_liftMatrix {N : M2 A} (hN : Cen N) (b : SlopeTestRemainingChoices S A) : Commute (d0 b) (lift0 N) :=
  diagScalar_commute_of_entries fun i j => (io_cen (hN i j) b).symm

theorem diagScalar_insert_commute_of_free {a : S} {N : M2 A} (hN : Cen N) {M : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 a M) :
    Commute (d0 (ins a (lift0 N))) M :=
  diagScalar_commute_of_entries fun i j => (comm_insL hN (hM i j)).symm

theorem cen_conjTranspose [StarRing A] {N : M2 A} (hN : Cen N) : Cen Nᴴ := by
  intro i j x
  have h := (hN j i (star x)).star_star
  rwa [star_star] at h

theorem ins_sandwich {a : S} {x : SlopeTestRemainingChoices S A} (hx : FreeOf a x) (M : M2 (SlopeTestRemainingChoices S A)) (y : SlopeTestRemainingChoices S A) :
    ins a (d0 x * M * d0 y) = x * ins a M * y := by
  unfold ins
  simp only [mul_diagScalar_apply, diagScalar_mul_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc, ← mul_assoc, (hx i j).eq]
  simp only [mul_assoc]

theorem diagScalar_sandwich_transpose (x y : SlopeTestRemainingChoices S A) (M : M2 (SlopeTestRemainingChoices S A)) :
    (d0 x * M * d0 y)ᵀ = d0 x * Mᵀ * d0 y := by
  ext1 i j
  rw [Matrix.transpose_apply, mul_diagScalar_apply, diagScalar_mul_apply, mul_diagScalar_apply, diagScalar_mul_apply,
    Matrix.transpose_apply]

theorem liftMatrix_mul_transpose_of_central {N : M2 A} (hN : Cen N) (M : M2 (SlopeTestRemainingChoices S A)) :
    (lift0 N * M)ᵀ = Mᵀ * lift0 Nᵀ := by
  ext1 i j
  rw [Matrix.transpose_apply, Matrix.mul_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun k _ => (io_cen (hN j k) (M k i)).eq

theorem mul_lift0_transpose {N : M2 A} (hN : Cen N) (M : M2 (SlopeTestRemainingChoices S A)) :
    (M * lift0 N)ᵀ = lift0 Nᵀ * Mᵀ := by
  ext1 i j
  rw [Matrix.transpose_apply, Matrix.mul_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun k _ => (io_cen (hN k i) (M j k)).eq.symm

end Basic

section Scalars

variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]

theorem io_algebraMap (k : K) : (io (algebraMap K A k) : SlopeTestRemainingChoices S A) = k • (1 : SlopeTestRemainingChoices S A) := by
  unfold io
  ext u v
  rw [Matrix.scalar_apply, Matrix.smul_apply, Matrix.diagonal_apply, Matrix.one_apply,
    Algebra.algebraMap_eq_smul_one]
  split_ifs <;> simp

theorem cen_Um (s : K) : Cen (Um (A := A) s) := by
  intro i j x
  fin_cases i <;> fin_cases j
  · exact Commute.one_left x
  · exact Commute.zero_left x
  · exact (Algebra.commute_algebraMap_left s x).neg_left
  · exact Commute.one_left x

theorem cen_Uinv (s : K) : Cen (Uinv (A := A) s) := by
  intro i j x
  fin_cases i <;> fin_cases j
  · exact Commute.one_left x
  · exact Commute.zero_left x
  · exact Algebra.commute_algebraMap_left s x
  · exact Commute.one_left x

theorem Um_mul_Uinv (s : K) : Um (A := A) s * Uinv s = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Um, Uinv, Matrix.mul_apply, Fin.sum_univ_two]

theorem Uinv_mul_Um (s : K) : Uinv (A := A) s * Um s = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Um, Uinv, Matrix.mul_apply, Fin.sum_univ_two]

theorem Um_conjTranspose_transpose (s : K) : ((Um (A := A) s)ᴴ)ᵀ = Um (star s) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Um, algebraMap_star_comm]

theorem Uinv_star_mul (s : K) : (Uinv (A := A) (star s))ᴴ * (Um (A := A) s)ᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Um, Uinv, Matrix.mul_apply, Fin.sum_univ_two, ← algebraMap_star_comm]

theorem Uinv_conj_mul (s : K) : (Uinv (A := A) s)ᴴ * (Um (A := A) s)ᴴ = 1 := by
  rw [← Matrix.conjTranspose_mul, Um_mul_Uinv, Matrix.conjTranspose_one]

theorem insL_Um (a : S) (s : K) :
    (ins a (lift0 (Um (A := A) s)) : SlopeTestRemainingChoices S A) = 1 - s • eU a 1 0 := by
  rw [← sum_eU_diag a]
  unfold ins lift0
  simp [Fin.sum_univ_two, Um, io_one, io_zero, io_neg, io_algebraMap]
  abel

theorem rh_entry_comm {a : S} {b : SlopeTestRemainingChoices S A} (hb : FreeOf a b) (D : K) (i j : Fin 2) :
    Commute b ((Rh0 a D : M2 (SlopeTestRemainingChoices S A)) i j) := by
  unfold Rh0 P0
  rw [Matrix.smul_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.one_apply]
  refine Commute.smul_right (Commute.sub_right (Commute.smul_right ?_ _) (hb j i).symm) _
  split_ifs
  · exact Commute.one_right _
  · exact Commute.zero_right _

theorem rht_entry_comm {a : S} {b : SlopeTestRemainingChoices S A} (hb : FreeOf a b) (D : K) (i j : Fin 2) :
    Commute b ((Rht0 a D : M2 (SlopeTestRemainingChoices S A)) i j) := by
  unfold Rht0 Q0
  rw [Matrix.smul_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.one_apply]
  refine Commute.smul_right (Commute.sub_right (Commute.smul_right ?_ _) (hb i j).symm) _
  split_ifs
  · exact Commute.one_right _
  · exact Commute.zero_right _

theorem diagScalar_commute_R_matrix {a : S} {b : SlopeTestRemainingChoices S A} (hb : FreeOf a b) (D : K) :
    Commute (d0 b) (Rh0 a D) := diagScalar_commute_of_entries (rh_entry_comm hb D)

theorem diagScalar_commute_transposed_R_matrix {a : S} {b : SlopeTestRemainingChoices S A} (hb : FreeOf a b) (D : K) :
    Commute (d0 b) (Rht0 a D) := diagScalar_commute_of_entries (rht_entry_comm hb D)

theorem freeOf2_rmatrix {a c : S} (h : c ≠ a) (D : K) : FreeOf2 c (Rh0 a D : M2 (SlopeTestRemainingChoices S A)) :=
  fun i j k l => rh_entry_comm (fun m n => (eU_comm_of_ne h k l m n).symm) D i j

theorem freeOf2_rmatrix_transpose {a c : S} (h : c ≠ a) (D : K) : FreeOf2 c (Rht0 a D : M2 (SlopeTestRemainingChoices S A)) :=
  fun i j k l => rht_entry_comm (fun m n => (eU_comm_of_ne h k l m n).symm) D i j

theorem UU_commute_flip (a : S) (s : K) :
    lift0 (Um (A := A) s) * d0 (ins a (lift0 (Um (A := A) s))) * P0 a =
      P0 a * (lift0 (Um (A := A) s) * d0 (ins a (lift0 (Um (A := A) s)))) := by
  rw [insL_Um]
  ext1 i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, lift0, d0, P0, Um, io_one, io_zero, io_neg,
      io_algebraMap, sub_mul, mul_sub, eU_mul_eU, smul_sub] <;> try module

theorem exchange_conj_through_partial_flip (b : S) (s : K) :
    d0 (ins b (lift0 (Um (A := A) (star s)))) * Q0 b * lift0 (Um (A := A) s)ᴴ =
      lift0 (Um (A := A) s)ᴴ * Q0 b * d0 (ins b (lift0 (Um (A := A) (star s)))) := by
  rw [insL_Um]
  ext1 i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, lift0, d0, Q0, Um, io_one, io_zero, io_neg,
      io_algebraMap, sub_mul, mul_sub, add_mul, neg_mul, eU_mul_eU, ← algebraMap_star_comm] <;>
    try module

end Scalars

section Words

variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]

theorem rhUU (a : S) (D s : K) :
    lift0 (Um (A := A) s) * d0 (ins a (lift0 (Um (A := A) s))) * Rh0 a D =
      Rh0 a D * (lift0 (Um (A := A) s) * d0 (ins a (lift0 (Um (A := A) s)))) := by
  unfold Rh0
  rw [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, UU_commute_flip, mul_smul_comm, smul_mul_assoc,
    mul_one, one_mul]

theorem rhtUU (b : S) (d s : K) :
    d0 (ins b (lift0 (Um (A := A) (star s)))) * Rht0 b d * lift0 (Um (A := A) s)ᴴ =
      lift0 (Um (A := A) s)ᴴ * Rht0 b d * d0 (ins b (lift0 (Um (A := A) (star s)))) := by
  have hc := (diagScalar_commute_liftMatrix (S := S) (cen_conjTranspose (cen_Um (A := A) s))
    (ins b (lift0 (Um (A := A) (star s))))).eq
  unfold Rht0
  simp only [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, exchange_conj_through_partial_flip, mul_one, hc]

theorem comm_of_inv {f fi x : A} (h1 : f * fi = 1) (h2 : fi * f = 1) (h : x * fi = fi * x) :
    f * x = x * f := by
  calc f * x = f * (x * fi) * f := by rw [mul_assoc, mul_assoc, h2, mul_one]
    _ = f * fi * x * f := by rw [h]; simp only [mul_assoc]
    _ = x * f := by rw [h1, one_mul]

theorem Tm_map_star (Y : K) (p c ci : A) :
    (Tm Y p c ci).map star = Tm (star Y) (star p) (star c) (star ci) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Tm, algebraMap_star_comm]

theorem letter_wave (σ : Site A) (f fi : A) (s : K) (l : Letter K S)
    (hW : IsWave f fi) (hc : f * σ.c = σ.c * f) (hci : f * σ.ci = σ.ci * f)
    (hp : σ.p * f = f * σ.p + algebraMap K A s * f * σ.c) :
    (if l.plus then Ts σ l.pt else (Ts σ l.pt).map star) * Matrix.diagonal (fun _ => f) *
        Uinv (if l.plus then s else star s) =
      Matrix.diagonal (fun _ => f) * (if l.plus then Ts σ l.pt else (Ts σ l.pt).map star) := by
  obtain ⟨h1, h2, h3⟩ := hW
  by_cases hl : l.plus
  · simp only [hl, if_true]
    exact (Formalism.YangianSpanCharacter.Final.T_PlaneWave K A σ.p σ.c σ.ci f s l.pt hc hci hp).2.2
  · simp only [hl, Bool.false_eq_true, if_false]
    unfold Ts
    rw [Tm_map_star]
    refine (Formalism.YangianSpanCharacter.Final.T_PlaneWave K A (star σ.p) (star σ.c) (star σ.ci) f (star s) (star l.pt)
      ?_ ?_ ?_).2.2
    · refine comm_of_inv h1 h2 ?_
      have := congrArg star hc
      rw [star_mul, star_mul, h3] at this
      exact this
    · refine comm_of_inv h1 h2 ?_
      have := congrArg star hci
      rw [star_mul, star_mul, h3] at this
      exact this
    · have hs := congrArg star hp
      rw [star_mul, star_add, star_mul, star_mul, star_mul, h3, ← algebraMap_star_comm] at hs
      have hz : ∀ x : A, algebraMap K A (star s) * x = x * algebraMap K A (star s) :=
        fun x => Algebra.commutes _ x
      calc star σ.p * f = f * (fi * star σ.p) * f := by
            rw [← mul_assoc, h1, one_mul]
        _ = f * star σ.p * (fi * f) + f * star σ.c * (fi * f) * algebraMap K A (star s) := by
            rw [hs, mul_add, add_mul]
            congr 1
            · simp only [mul_assoc]
            · simp only [mul_assoc]
              rw [hz f]
        _ = f * star σ.p + algebraMap K A (star s) * f * star σ.c := by
            rw [h2, mul_one, mul_one, mul_assoc (algebraMap K A (star s)), hz]

theorem vlet_wave (σ : Site A) (f fi : A) (s : K) (l : Letter K S)
    (hW : IsWave f fi) (hc : f * σ.c = σ.c * f) (hci : f * σ.ci = σ.ci * f)
    (hp : σ.p * f = f * σ.p + algebraMap K A s * f * σ.c) :
    vlet σ l * (io f * ins l.intersection_update_fsHerm_neg_one (lift0 (Uinv (A := A) (if l.plus then s else star s)))) =
      io f * vlet σ l := by
  unfold vlet
  rw [← insL_diag l.intersection_update_fsHerm_neg_one f, ← insL_mul, ← insL_mul, ← insL_mul, ← mul_assoc,
    letter_wave σ f fi s l hW hc hci hp]

theorem free_bT (σ : Site A) (w : List (Letter K S)) (c : S) (hc : c ∉ w.map Letter.intersection_update_fsHerm_neg_one) :
    FreeOf c (bT σ w) := by
  induction w with
  | nil => exact free_one c
  | cons l w ih =>
    rw [List.map_cons, List.mem_cons, not_or] at hc
    exact free_mul (free_insL hc.1 _) (ih hc.2)

theorem planeWaveVec (σ : Site A) (f fi : A) (s : K) (w : List (Letter K S))
    (hW : IsWave f fi) (hc : f * σ.c = σ.c * f) (hci : f * σ.ci = σ.ci * f)
    (hp : σ.p * f = f * σ.p + algebraMap K A s * f * σ.c) (hw : (w.map Letter.intersection_update_fsHerm_neg_one).Nodup) :
    bT σ w * Vw f s w = io f * bT σ w := by
  induction w with
  | nil => simp [bT, Vw, UUiw]
  | cons l w ih =>
    rw [List.map_cons, List.nodup_cons] at hw
    have ih' : bT σ w * (io f * UUiw s w) = io f * bT σ w := ih hw.2
    have c1 : Commute (bT σ w) (ins l.intersection_update_fsHerm_neg_one (lift0 (Uinv (A := A) (if l.plus then s else star s)))) :=
      comm_insL (cen_Uinv _) (free_bT σ w _ hw.1)
    have c2 : Commute (io f : SlopeTestRemainingChoices S A)
        (ins l.intersection_update_fsHerm_neg_one (lift0 (Uinv (A := A) (if l.plus then s else star s)))) :=
      comm_insL (cen_Uinv _) (free_io _ f)
    show vlet σ l * bT σ w *
      (io f * (ins l.intersection_update_fsHerm_neg_one (lift0 (Uinv (A := A) (if l.plus then s else star s))) * UUiw s w)) =
      io f * (vlet σ l * bT σ w)
    rw [c2.left_comm, mul_assoc, c1.left_comm, ih', ← c2.left_comm, ← mul_assoc, ← mul_assoc,
      mul_assoc (vlet σ l), vlet_wave σ f fi s l hW hc hci hp, mul_assoc]

theorem freeOf_transfer_word_matrix (QQ : K → M2 A) (w : List (Letter K S)) (c : S)
    (hc : c ∉ w.map Letter.intersection_update_fsHerm_neg_one) (Y : K) : FreeOf2 c (TTw QQ w Y) := by
  induction w with
  | nil => exact freeOf2_lift c _
  | cons l w ih =>
    rw [List.map_cons, List.mem_cons, not_or] at hc
    unfold TTw
    split_ifs
    · exact freeOf2_mul (ih hc.2) (freeOf2_rmatrix hc.1 _)
    · exact freeOf2_mul (freeOf2_rmatrix_transpose hc.1 _) (ih hc.2)

theorem free_RRw (QQ : K → M2 A) (w : List (Letter K S)) (c : S)
    (hc : c ∉ w.map Letter.intersection_update_fsHerm_neg_one) : FreeOf c (RRw QQ w) := by
  induction w with
  | nil => exact free_one c
  | cons l w ih =>
    rw [List.map_cons, List.mem_cons, not_or] at hc
    unfold RRw
    refine free_mul (ih hc.2) (ins_free hc.1 _ ?_)
    split_ifs
    · exact freeOf_transfer_word_matrix QQ w c hc.2 _
    · exact freeOf2_transpose (freeOf_transfer_word_matrix QQ w c hc.2 _)

theorem free_UUw (s : K) (w : List (Letter K S)) (c : S) (hc : c ∉ w.map Letter.intersection_update_fsHerm_neg_one) :
    FreeOf c (UUw s w : SlopeTestRemainingChoices S A) := by
  induction w with
  | nil => exact free_one c
  | cons l w ih =>
    rw [List.map_cons, List.mem_cons, not_or] at hc
    exact free_mul (free_insL hc.1 _) (ih hc.2)

theorem free_UUiw (s : K) (w : List (Letter K S)) (c : S) (hc : c ∉ w.map Letter.intersection_update_fsHerm_neg_one) :
    FreeOf c (UUiw s w : SlopeTestRemainingChoices S A) := by
  induction w with
  | nil => exact free_one c
  | cons l w ih =>
    rw [List.map_cons, List.mem_cons, not_or] at hc
    exact free_mul (free_insL hc.1 _) (ih hc.2)

theorem free_Vw (f : A) (s : K) (w : List (Letter K S)) (c : S) (hc : c ∉ w.map Letter.intersection_update_fsHerm_neg_one) :
    FreeOf c (Vw f s w) := free_mul (free_io c f) (free_UUiw s w c hc)

theorem free_Viw (fi : A) (s : K) (w : List (Letter K S)) (c : S) (hc : c ∉ w.map Letter.intersection_update_fsHerm_neg_one) :
    FreeOf c (Viw fi s w) := free_mul (free_UUw s w c hc) (free_io c fi)

end Words

section Steps

theorem rr_step {B : Type*} [Ring B] [StarRing B] {V Vi RR TA W L R : B}
    (h1 : V * Vi = 1) (h3 : star V * RR * V = RR) (hWV : Commute W V)
    (hsRR : Commute (star W) RR) (hsV : Commute (star W) V)
    (hT : Vi * TA * V = L * TA * R) (hL : star W * L = 1) (hR : R * W = 1) :
    star (W * V) * (RR * TA) * (W * V) = RR * TA := by
  have k : TA * V = V * (L * TA * R) := by
    rw [← hT]; simp only [← mul_assoc]; rw [h1, one_mul]
  calc star (W * V) * (RR * TA) * (W * V)
      = star V * (star W * RR) * (TA * V) * W := by
        rw [star_mul, hWV.eq]; simp only [mul_assoc]
    _ = star V * (RR * star W) * (V * (L * TA * R)) * W := by rw [hsRR.eq, k]
    _ = star V * RR * (star W * V) * (L * TA * R) * W := by simp only [mul_assoc]
    _ = star V * RR * (V * star W) * (L * TA * R) * W := by rw [hsV.eq]
    _ = (star V * RR * V) * (star W * L) * TA * (R * W) := by simp only [mul_assoc]
    _ = RR * TA := by rw [h3, hL, hR, mul_one, mul_one]

variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]

theorem insL_Um_Uinv (a : S) (s : K) :
    (ins a (lift0 (Um (A := A) s)) : SlopeTestRemainingChoices S A) * ins a (lift0 (Uinv (A := A) s)) = 1 := by
  rw [← insL_mul, Um_mul_Uinv, insL_one]

theorem insL_Uinv_Um (a : S) (s : K) :
    (ins a (lift0 (Uinv (A := A) s)) : SlopeTestRemainingChoices S A) * ins a (lift0 (Um (A := A) s)) = 1 := by
  rw [← insL_mul, Uinv_mul_Um, insL_one]

theorem plus_TT (a : S) (s D : K) {V Vi : SlopeTestRemainingChoices S A} {T : M2 (SlopeTestRemainingChoices S A)}
    (hV : FreeOf a V) (hT : FreeOf2 a T)
    (h4 : d0 Vi * T * d0 V = lift0 (Um (A := A) s)ᴴ * T * lift0 (Um (A := A) s)) :
    d0 (ins a (lift0 (Um (A := A) s)) * Vi) * (T * Rh0 a D) *
        d0 (ins a (lift0 (Uinv (A := A) s)) * V) =
      lift0 (Um (A := A) s)ᴴ * (T * Rh0 a D) * lift0 (Um (A := A) s) := by
  set Ua : SlopeTestRemainingChoices S A := ins a (lift0 (Um (A := A) s)) with hUa
  set Uia : SlopeTestRemainingChoices S A := ins a (lift0 (Uinv (A := A) s)) with hUia
  set U0 : M2 (SlopeTestRemainingChoices S A) := lift0 (Um (A := A) s) with hU0
  set UH : M2 (SlopeTestRemainingChoices S A) := lift0 (Um (A := A) s)ᴴ with hUH
  set Rh : M2 (SlopeTestRemainingChoices S A) := Rh0 a D with hRh
  have i1 : d0 Ua * d0 Uia = 1 := by rw [← diagScalar_mul, hUa, hUia, insL_Um_Uinv, d0_one]
  have i2 : d0 Uia * d0 Ua = 1 := by rw [← diagScalar_mul, hUa, hUia, insL_Uinv_Um, d0_one]
  have cVU : Commute (d0 V) (d0 Uia) := diagScalar_commute_diagScalar (comm_insL (cen_Uinv s) hV)
  have cVR : Commute (d0 V) Rh := diagScalar_commute_R_matrix hV D
  have cU0 : Commute (d0 Ua) U0 := diagScalar_commute_liftMatrix (cen_Um s) _
  have cUH : Commute (d0 Uia) UH := diagScalar_commute_liftMatrix (cen_conjTranspose (cen_Um s)) _
  have cT : Commute (d0 Uia) T := diagScalar_insert_commute_of_free (cen_Uinv s) hT
  have hR : U0 * d0 Ua * Rh = Rh * (U0 * d0 Ua) := rhUU a D s
  have e1 : Rh * (d0 Uia * d0 V) = d0 V * (Rh * d0 Uia) := by
    rw [← cVU.eq, ← mul_assoc, ← cVR.eq, mul_assoc]
  have e2 : U0 * (Rh * d0 Uia) = d0 Uia * (Rh * U0) := by
    calc U0 * (Rh * d0 Uia) = d0 Uia * (d0 Ua * U0) * Rh * d0 Uia := by
          rw [← mul_assoc (d0 Uia), i2, one_mul, mul_assoc]
      _ = d0 Uia * (U0 * d0 Ua * Rh) * d0 Uia := by rw [cU0.eq]; simp only [mul_assoc]
      _ = d0 Uia * (Rh * U0) * (d0 Ua * d0 Uia) := by rw [hR]; simp only [mul_assoc]
      _ = d0 Uia * (Rh * U0) := by rw [i1, mul_one]
  have e3 : d0 Ua * (UH * (T * d0 Uia)) = UH * T := by
    rw [← cT.eq, ← mul_assoc UH, ← cUH.eq, mul_assoc, ← mul_assoc, i1, one_mul]
  calc d0 (Ua * Vi) * (T * Rh) * d0 (Uia * V)
      = d0 Ua * ((d0 Vi * T * d0 V) * (Rh * d0 Uia)) := by
        rw [diagScalar_mul, diagScalar_mul]; simp only [mul_assoc]; rw [e1]
    _ = d0 Ua * (UH * (T * (U0 * (Rh * d0 Uia)))) := by rw [h4]; simp only [mul_assoc]
    _ = (d0 Ua * (UH * (T * d0 Uia))) * (Rh * U0) := by rw [e2]; simp only [mul_assoc]
    _ = UH * (T * Rh) * U0 := by rw [e3]; simp only [mul_assoc]

theorem minus_TT (b : S) (s d : K) {V Vi : SlopeTestRemainingChoices S A} {T : M2 (SlopeTestRemainingChoices S A)}
    (hV : FreeOf b V) (hVi : FreeOf b Vi) (hT : FreeOf2 b T)
    (h4 : d0 Vi * T * d0 V = lift0 (Um (A := A) s)ᴴ * T * lift0 (Um (A := A) s)) :
    d0 (ins b (lift0 (Um (A := A) (star s))) * Vi) * (Rht0 b d * T) *
        d0 (ins b (lift0 (Uinv (A := A) (star s))) * V) =
      lift0 (Um (A := A) s)ᴴ * (Rht0 b d * T) * lift0 (Um (A := A) s) := by
  set Ub : SlopeTestRemainingChoices S A := ins b (lift0 (Um (A := A) (star s))) with hUb
  set Uib : SlopeTestRemainingChoices S A := ins b (lift0 (Uinv (A := A) (star s))) with hUib
  set U0 : M2 (SlopeTestRemainingChoices S A) := lift0 (Um (A := A) s) with hU0
  set UH : M2 (SlopeTestRemainingChoices S A) := lift0 (Um (A := A) s)ᴴ with hUH
  set Rh : M2 (SlopeTestRemainingChoices S A) := Rht0 b d with hRh
  have i1 : d0 Ub * d0 Uib = 1 := by rw [← diagScalar_mul, hUb, hUib, insL_Um_Uinv, d0_one]
  have cVU : Commute (d0 V) (d0 Uib) := diagScalar_commute_diagScalar (comm_insL (cen_Uinv _) hV)
  have cVR : Commute (d0 Vi) Rh := diagScalar_commute_transposed_R_matrix hVi d
  have cU0 : Commute (d0 Ub) U0 := diagScalar_commute_liftMatrix (cen_Um s) _
  have cT : Commute (d0 Ub) T := diagScalar_insert_commute_of_free (cen_Um _) hT
  have hR : d0 Ub * Rh * UH = UH * Rh * d0 Ub := rhtUU b d s
  calc d0 (Ub * Vi) * (Rh * T) * d0 (Uib * V)
      = d0 Ub * (d0 Vi * Rh) * T * (d0 Uib * d0 V) := by
        rw [diagScalar_mul, diagScalar_mul]; simp only [mul_assoc]
    _ = d0 Ub * Rh * (d0 Vi * T * d0 V) * d0 Uib := by
        rw [cVR.eq, ← cVU.eq]; simp only [mul_assoc]
    _ = (d0 Ub * Rh * UH) * T * U0 * d0 Uib := by rw [h4]; simp only [mul_assoc]
    _ = UH * Rh * (d0 Ub * T) * U0 * d0 Uib := by rw [hR]; simp only [mul_assoc]
    _ = UH * Rh * T * (d0 Ub * U0) * d0 Uib := by rw [cT.eq]; simp only [mul_assoc]
    _ = UH * Rh * T * U0 * (d0 Ub * d0 Uib) := by rw [cU0.eq]; simp only [mul_assoc]
    _ = UH * (Rh * T) * U0 := by rw [i1, mul_one]; simp only [mul_assoc]

theorem plus_RR (a : S) (s : K) {V Vi RR : SlopeTestRemainingChoices S A} {T : M2 (SlopeTestRemainingChoices S A)}
    (hV : FreeOf a V) (hVi : FreeOf a Vi) (hRR : FreeOf a RR) (hT : FreeOf2 a T)
    (h1 : V * Vi = 1) (h3 : star V * RR * V = RR)
    (h4 : d0 Vi * T * d0 V = lift0 (Um (A := A) s)ᴴ * T * lift0 (Um (A := A) s)) :
    star (ins a (lift0 (Uinv (A := A) s)) * V) * (RR * ins a T) *
        (ins a (lift0 (Uinv (A := A) s)) * V) = RR * ins a T := by
  have hs : star (ins a (lift0 (Uinv (A := A) s)) : SlopeTestRemainingChoices S A) = ins a (lift0 (Uinv (A := A) s)ᴴ) :=
    insL_star a _
  refine rr_step (Vi := Vi) (L := ins a (lift0 (Um (A := A) s)ᴴ)) (R := ins a (lift0 (Um (A := A) s)))
    h1 h3 (comm_insL (cen_Uinv s) hV).symm ?_ ?_ ?_ ?_ (insL_Um_Uinv a s)
  · rw [hs]; exact (comm_insL (cen_conjTranspose (cen_Uinv s)) hRR).symm
  · rw [hs]; exact (comm_insL (cen_conjTranspose (cen_Uinv s)) hV).symm
  · rw [← ins_sandwich hVi, h4, ins_mul a _ _ (freeOf2_mul (freeOf2_lift a _) hT),
      ins_mul a _ _ (freeOf2_lift a _)]
  · rw [hs, ← insL_mul, Uinv_conj_mul, insL_one]

theorem minus_RR (b : S) (s : K) {V Vi RR : SlopeTestRemainingChoices S A} {T : M2 (SlopeTestRemainingChoices S A)}
    (hV : FreeOf b V) (hVi : FreeOf b Vi) (hRR : FreeOf b RR) (hT : FreeOf2 b T)
    (h1 : V * Vi = 1) (h3 : star V * RR * V = RR)
    (h4 : d0 Vi * T * d0 V = lift0 (Um (A := A) s)ᴴ * T * lift0 (Um (A := A) s)) :
    star (ins b (lift0 (Uinv (A := A) (star s))) * V) * (RR * ins b Tᵀ) *
        (ins b (lift0 (Uinv (A := A) (star s))) * V) = RR * ins b Tᵀ := by
  have hs : star (ins b (lift0 (Uinv (A := A) (star s))) : SlopeTestRemainingChoices S A) =
      ins b (lift0 (Uinv (A := A) (star s))ᴴ) := insL_star b _
  refine rr_step (Vi := Vi) (L := ins b (lift0 (Um (A := A) s)ᵀ))
    (R := ins b (lift0 (Um (A := A) (star s))))
    h1 h3 (comm_insL (cen_Uinv _) hV).symm ?_ ?_ ?_ ?_ (insL_Um_Uinv b _)
  · rw [hs]; exact (comm_insL (cen_conjTranspose (cen_Uinv _)) hRR).symm
  · rw [hs]; exact (comm_insL (cen_conjTranspose (cen_Uinv _)) hV).symm
  · rw [← ins_sandwich hVi, ← diagScalar_sandwich_transpose, h4, mul_lift0_transpose (cen_Um s),
      liftMatrix_mul_transpose_of_central (cen_conjTranspose (cen_Um s)), Um_conjTranspose_transpose, ← mul_assoc,
      ins_mul b _ _ (freeOf2_mul (freeOf2_lift b _) (freeOf2_transpose hT)),
      ins_mul b _ _ (freeOf2_lift b _)]
  · rw [hs, ← insL_mul, Uinv_star_mul, insL_one]

theorem Vw_cons (f : A) (s : K) (l : Letter K S) (w : List (Letter K S)) :
    Vw f s (l :: w) =
      ins l.intersection_update_fsHerm_neg_one (lift0 (Uinv (A := A) (if l.plus then s else star s))) * Vw f s w := by
  show io f * (ins l.intersection_update_fsHerm_neg_one (lift0 (Uinv (A := A) (if l.plus then s else star s))) * UUiw s w) =
    ins l.intersection_update_fsHerm_neg_one (lift0 (Uinv (A := A) (if l.plus then s else star s))) * (io f * UUiw s w)
  exact (comm_insL (cen_Uinv _) (free_io _ f)).left_comm _

theorem Viw_cons (fi : A) (s : K) (l : Letter K S) (w : List (Letter K S)) :
    Viw fi s (l :: w) =
      ins l.intersection_update_fsHerm_neg_one (lift0 (Um (A := A) (if l.plus then s else star s))) * Viw fi s w := by
  show ins l.intersection_update_fsHerm_neg_one (lift0 (Um (A := A) (if l.plus then s else star s))) * UUw s w * io fi =
    ins l.intersection_update_fsHerm_neg_one (lift0 (Um (A := A) (if l.plus then s else star s))) * (UUw s w * io fi)
  exact mul_assoc _ _ _

theorem planeWaveWord (QQ : K → M2 A) (f fi : A) (s : K) (w : List (Letter K S))
    (hW : IsWave f fi) (hQ : WaveQQ QQ f fi s) (hw : (w.map Letter.intersection_update_fsHerm_neg_one).Nodup) :
    Vw f s w * Viw fi s w = 1 ∧ Viw fi s w * Vw f s w = 1 ∧
    star (Vw f s w) * RRw QQ w * Vw f s w = RRw QQ w ∧
    ∀ Y, d0 (Viw fi s w) * TTw QQ w Y * d0 (Vw f s w) =
      lift0 (Um (A := A) s)ᴴ * TTw QQ w Y * lift0 (Um (A := A) s) := by
  induction w with
  | nil =>
    obtain ⟨h1, h2, h3⟩ := hW
    have eV : (Vw f s ([] : List (Letter K S)) : SlopeTestRemainingChoices S A) = io f := mul_one _
    have eVi : (Viw fi s ([] : List (Letter K S)) : SlopeTestRemainingChoices S A) = io fi := one_mul _
    rw [eV, eVi]
    refine ⟨by rw [← io_mul, h1, io_one], by rw [← io_mul, h2, io_one], ?_, ?_⟩
    · show star (io f) * 1 * io f = 1
      rw [io_star, h3, mul_one, ← io_mul, h2, io_one]
    · intro Y
      show d0 (io fi) * lift0 (QQ Y) * d0 (io f) = _ * lift0 (QQ Y) * _
      rw [← liftMatrix_diagonal_eq_diagScalar, ← liftMatrix_diagonal_eq_diagScalar, ← lift_reduction_mul, ← lift_reduction_mul, hQ Y, lift_reduction_mul, lift_reduction_mul]
  | cons l w ih =>
    rw [List.map_cons, List.nodup_cons] at hw
    obtain ⟨h1, h2, h3, h4⟩ := ih hw.2
    have hV := free_Vw f s w l.intersection_update_fsHerm_neg_one hw.1
    have hVi := free_Viw fi s w l.intersection_update_fsHerm_neg_one hw.1
    have hRR := free_RRw QQ w l.intersection_update_fsHerm_neg_one hw.1
    have hT := freeOf_transfer_word_matrix QQ w l.intersection_update_fsHerm_neg_one hw.1
    rw [Vw_cons, Viw_cons]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [mul_assoc, (comm_insL (cen_Um _) hV).left_comm, h1, mul_one, insL_Uinv_Um]
    · rw [mul_assoc, (comm_insL (cen_Uinv _) hVi).left_comm, h2, mul_one, insL_Um_Uinv]
    · unfold RRw
      by_cases hl : l.plus
      · simp only [hl, if_true]
        exact plus_RR l.intersection_update_fsHerm_neg_one s hV hVi hRR (hT _) h1 h3 (h4 _)
      · simp only [hl, Bool.false_eq_true, if_false]
        exact minus_RR l.intersection_update_fsHerm_neg_one s hV hVi hRR (hT _) h1 h3 (h4 _)
    · intro Y
      unfold TTw
      by_cases hl : l.plus
      · simp only [hl, if_true]
        exact plus_TT l.intersection_update_fsHerm_neg_one s _ hV (hT _) (h4 _)
      · simp only [hl, Bool.false_eq_true, if_false]
        exact minus_TT l.intersection_update_fsHerm_neg_one s _ hV hVi (hT _) (h4 _)

end Steps

end Formalism.FourierDecayAlt.P.Wd11

namespace Formalism.FourierDecayAlt.P

theorem R_matrix_UU_relation : Formalism.FourierDecayAlt.Wd.RhUU := by
  intro K A S _ _ _ _ _ _ _ _ a D s
  exact Wd11.rhUU a D s

theorem transposed_R_matrix_UU_relation : Formalism.FourierDecayAlt.Wd.RhtUU := by
  intro K A S _ _ _ _ _ _ _ _ b d s
  exact Wd11.rhtUU b d s

theorem plane_wave_vector_identity : Formalism.FourierDecayAlt.Wd.PlaneWaveVec := by
  intro K A S _ _ _ _ _ _ _ _ σ f fi s w hW hc hci hp hw
  exact Wd11.planeWaveVec σ f fi s w hW hc hci hp hw

theorem plane_wave_word_identity : Formalism.FourierDecayAlt.Wd.PlaneWaveWord := by
  intro K A S _ _ _ _ _ _ _ _ QQ f fi s w hW hQ hw
  exact Wd11.planeWaveWord QQ f fi s w hW hQ hw

end Formalism.FourierDecayAlt.P
