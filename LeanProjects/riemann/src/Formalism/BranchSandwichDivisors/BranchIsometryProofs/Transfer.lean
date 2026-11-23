import Mathlib
import Formalism.BranchSandwichDivisors.StatementL
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.TransferMean
import Formalism.MeanHeightDescent.AverageDegreeBounds.GoodBadCut
import Formalism.HarderNarasimhan.ShiftInvariance

open Module NumberField
open scoped Matrix

noncomputable section

namespace Formalism.BranchingDeterminantCap

open Formalism.HN

namespace PrismTransfer

section Basic

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]

theorem natCast_smul_eq (n : ℕ) (x : V) : (n : 𝓞 K) • x = (n : K) • x := by
  simp only [Nat.cast_smul_eq_nsmul]

theorem degD_le_muMax (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (N M : Submodule (𝓞 K) V) (hM : M.FG) (hNM : N ≤ M) :
    degD b X N ≤ (rkK N : ℝ) * muMaxDef b X M := by
  unfold degD
  by_cases hb : N = ⊥
  · rw [hb, Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.rkK_bot]; simp
  · have hM0 : M ≠ ⊥ := fun h => hb (le_bot_iff.1 (h ▸ hNM))
    have hlat := (place_lattice_structure K V ι b X hX M hM).1
    have hmax := ((slope_characterization (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) M hlat hM0).1
      (muMax (Formalism.HermitianLatticesTheory.realize b X) M)).1 le_rfl N hNM
    have hr0 : rk (Formalism.HermitianLatticesTheory.realize b X) N ≠ 0 := fun h =>
      hb (((saturation_basic_properties (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) M hlat).2.2.2.1 N hNM).1 h)
    have hrpos : (0 : ℝ) < (rk (Formalism.HermitianLatticesTheory.realize b X) N : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hr0
    have hs : slope (Formalism.HermitianLatticesTheory.realize b X) N ≤ muMax (Formalism.HermitianLatticesTheory.realize b X) M := by
      change deg (Formalism.HermitianLatticesTheory.realize b X) N / (rk (Formalism.HermitianLatticesTheory.realize b X) N : ℝ) ≤ _
      rw [div_le_iff₀ hrpos]
      exact hmax
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    unfold muDef muMaxDef
    linarith

end Basic

end PrismTransfer

open PrismTransfer

theorem passageLat_of (hLC : LevelCompare) : PassageLat := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX S _ Rs nS latticeAtBaseLevel RPs R0 R1 G h0 h1 nbar de HH0 hP0 hPs hR0 hR1
    hh0 hh0G hh1 hh1G hR0le hR0s hR1le hR1s hRs hrk0 hrks hdegs hdeg0 hnbar hde0 hde hnS hHH
  obtain ⟨a0, a0'⟩ := hLC K V ι b X hX latticeAtBaseLevel R0 h0 hP0 hR0 hh0 hR0le hR0s
  obtain ⟨a1, _⟩ := hLC K V ι b X hX RPs R1 h1 hPs hR1 hh1 hR1le hR1s
  have hl0 : Real.log h0 ≤ Real.log G :=
    Real.log_le_log (by exact_mod_cast hh0) (by exact_mod_cast hh0G)
  have hl1 : Real.log h1 ≤ Real.log G :=
    Real.log_le_log (by exact_mod_cast hh1) (by exact_mod_cast hh1G)
  have hla : 0 ≤ Real.log G := Real.log_natCast_nonneg G
  have hP0ne : latticeAtBaseLevel ≠ ⊥ := fun h => hR0 (le_bot_iff.1 (h ▸ hR0le))
  have hrkpos : (0 : ℝ) < (rkK latticeAtBaseLevel : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.rkK_ne_zero b latticeAtBaseLevel hP0ne)
  have key := (meanTransferBound S (fun s => (rkK (Rs s) : ℝ)) (fun s => (nS s : ℝ))
    (fun s => degD b X (Rs s)) nbar de (Real.log G) 1 HH0 (muDef b X latticeAtBaseLevel) (muDef b X RPs)
    (muDef b (scaleFrame (Real.sqrt h0) X) R0) (muDef b (scaleFrame (Real.sqrt h1) X) R1)
    hnbar hde0 hde hla zero_le_one (fun s => Nat.cast_nonneg _) (by rw [← hrk0]; exact hrkpos) hnS
    (by linarith) (by linarith)
    (fun s => by
      have h5 := degD_le_muMax b X hX (Rs s) latticeAtBaseLevel hP0 (hRs s)
      have h6 : muMaxDef b X latticeAtBaseLevel ≤ HH0 + 1 * Real.log G := by
        have := (abs_le.1 a0').1
        linarith
      exact h5.trans (mul_le_mul_of_nonneg_left h6 (Nat.cast_nonneg _)))
    (by
      rw [← hrks]
      have : muDef b X RPs * (rkK RPs : ℝ) = degD b X RPs := by unfold degD; ring
      rw [this]; exact hdegs)
    (by
      rw [← hrk0]
      have : muDef b X latticeAtBaseLevel * (rkK latticeAtBaseLevel : ℝ) = degD b X latticeAtBaseLevel := by unfold degD; ring
      rw [this]; exact hdeg0)).2
  have e1 : (2 * (1 : ℝ) + 2) = 4 := by norm_num
  have e2 : (2 * (1 : ℝ) + 21 / 2) = 25 / 2 := by norm_num
  rw [e1, e2] at key
  exact key

namespace PrismTransfer

section Mat

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem sigma_norm_sq {n : ℕ} (z : EuclideanSpace ℂ (Σ _ : Fin n, ι)) :
    ‖z‖ ^ 2 = ∑ i, ‖(WithLp.toLp 2 (fun j => z ⟨i, j⟩) : EuclideanSpace ℂ ι)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EuclideanSpace.norm_sq_eq]
  try rfl

theorem apply_le_of_norm_le (M : Matrix ι ι ℂ)
    (hM : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖ ≤ 1)
    (z : EuclideanSpace ℂ ι) : ‖Matrix.toEuclideanLin M z‖ ≤ ‖z‖ := by
  have h := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)).le_opNorm z
  calc ‖Matrix.toEuclideanLin M z‖
      ≤ ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)‖ * ‖z‖ := h
    _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hM (norm_nonneg z)
    _ = ‖z‖ := one_mul _

theorem row_norm_le {n : ℕ} (M : Fin n → Matrix ι ι ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hM : ∀ i, ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (M i))‖ ≤ 1)
    (R : Matrix ι (Σ _ : Fin n, ι) ℂ) (hR : ∀ k p, R k p = (c : ℂ) * M p.1 k p.2) :
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin R)‖ ≤ c * Real.sqrt n := by
  have hsq : 0 ≤ c * Real.sqrt n := mul_nonneg hc (Real.sqrt_nonneg _)
  refine ContinuousLinearMap.opNorm_le_bound _ hsq fun z => ?_
  let zs : Fin n → EuclideanSpace ℂ ι := fun i => WithLp.toLp 2 (fun j => z ⟨i, j⟩)
  have hdec : LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin R) z =
      ∑ i, (c : ℂ) • Matrix.toEuclideanLin (M i) (zs i) := by
    ext k
    simp [zs, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, Fintype.sum_sigma, hR,
      Finset.mul_sum, mul_assoc, Finset.sum_apply]
  have hnorm : ∑ i, ‖zs i‖ ^ 2 = ‖z‖ ^ 2 := (sigma_norm_sq z).symm
  have hzs : ∑ i, ‖zs i‖ ≤ Real.sqrt n * ‖z‖ := by
    have hcs : (∑ i, ‖zs i‖) ^ 2 ≤ (Finset.univ : Finset (Fin n)).card * ∑ i, ‖zs i‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    rw [Finset.card_univ, Fintype.card_fin, hnorm] at hcs
    have h0 : 0 ≤ ∑ i, ‖zs i‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
    rw [← Real.sqrt_sq h0, ← Real.sqrt_sq (norm_nonneg z), ← Real.sqrt_mul (Nat.cast_nonneg _)]
    exact Real.sqrt_le_sqrt hcs
  rw [hdec]
  calc ‖∑ i, (c : ℂ) • Matrix.toEuclideanLin (M i) (zs i)‖
      ≤ ∑ i, ‖(c : ℂ) • Matrix.toEuclideanLin (M i) (zs i)‖ := norm_sum_le _ _
    _ = ∑ i, c * ‖Matrix.toEuclideanLin (M i) (zs i)‖ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hc]
    _ ≤ ∑ i, c * ‖zs i‖ := by
        gcongr with i
        exact apply_le_of_norm_le (M i) (hM i) (zs i)
    _ = c * ∑ i, ‖zs i‖ := by rw [Finset.mul_sum]
    _ ≤ c * (Real.sqrt n * ‖z‖) := by gcongr
    _ = c * Real.sqrt n * ‖z‖ := by ring

theorem col_norm_le {n : ℕ} (M : Fin n → Matrix ι ι ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hM : ∀ i, ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (M i))‖ ≤ 1)
    (C : Matrix (Σ _ : Fin n, ι) ι ℂ) (hC : ∀ p k, C p k = (c : ℂ) * M p.1 p.2 k) :
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin C)‖ ≤ c * Real.sqrt n := by
  have hsq : 0 ≤ c * Real.sqrt n := mul_nonneg hc (Real.sqrt_nonneg _)
  refine ContinuousLinearMap.opNorm_le_bound _ hsq fun z => ?_
  have hblk : ∀ i, (WithLp.toLp 2 (fun j =>
      (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin C) z) ⟨i, j⟩) : EuclideanSpace ℂ ι) =
      (c : ℂ) • Matrix.toEuclideanLin (M i) z := by
    intro i
    ext j
    simp [Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, hC, Finset.mul_sum, mul_assoc]
  have hsq2 : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin C) z‖ ^ 2 ≤
      (c * Real.sqrt n * ‖z‖) ^ 2 := by
    rw [sigma_norm_sq]
    simp only [hblk]
    calc ∑ i, ‖(c : ℂ) • Matrix.toEuclideanLin (M i) z‖ ^ 2
        ≤ ∑ _i : Fin n, (c * ‖z‖) ^ 2 := by
          gcongr with i
          rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hc]
          exact mul_le_mul_of_nonneg_left (apply_le_of_norm_le (M i) (hM i) z) hc
      _ = (c * Real.sqrt n * ‖z‖) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          have hs := Real.sq_sqrt (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
          calc (n : ℝ) * (c * ‖z‖) ^ 2 = (c * ‖z‖) ^ 2 * (Real.sqrt n) ^ 2 := by rw [hs]; ring
            _ = (c * Real.sqrt n * ‖z‖) ^ 2 := by ring
  have hy : 0 ≤ c * Real.sqrt n * ‖z‖ := mul_nonneg hsq (norm_nonneg z)
  nlinarith [norm_nonneg (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin C) z)]

theorem blockDiag_mul_inv {n : ℕ} (Y : Matrix ι ι ℂ) (hY : IsUnit Y.det) :
    Matrix.blockDiagonal' (fun _ : Fin n => Y) * Matrix.blockDiagonal' (fun _ : Fin n => Y⁻¹) = 1 := by
  rw [← Matrix.blockDiagonal'_mul]
  have h : (fun _ : Fin n => Y * Y⁻¹) = fun _ : Fin n => (1 : Matrix ι ι ℂ) := by
    funext _
    exact Matrix.mul_nonsing_inv Y hY
  rw [h]
  exact Matrix.blockDiagonal'_one

theorem blockDiag_det {n : ℕ} (Y : Matrix ι ι ℂ) (hY : IsUnit Y.det) :
    IsUnit (Matrix.blockDiagonal' (fun _ : Fin n => Y)).det := Matrix.isUnit_det_of_right_inverse (blockDiag_mul_inv Y hY)

theorem blockDiag_inv {n : ℕ} (Y : Matrix ι ι ℂ) (hY : IsUnit Y.det) :
    (Matrix.blockDiagonal' (fun _ : Fin n => Y))⁻¹ = Matrix.blockDiagonal' (fun _ : Fin n => Y⁻¹) := Matrix.inv_eq_right_inv (blockDiag_mul_inv Y hY)

theorem mul_blockDiag_apply {n : ℕ} {κ : Type} (N : Matrix κ (Σ _ : Fin n, ι) ℂ) (Y : Matrix ι ι ℂ)
    (k : κ) (i : Fin n) (j : ι) :
    (N * Matrix.blockDiagonal' (fun _ : Fin n => Y)) k ⟨i, j⟩ = ∑ l, N k ⟨i, l⟩ * Y l j := by
  rw [Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single i]
  · exact Finset.sum_congr rfl fun l _ => by rw [Matrix.blockDiagonal'_apply_eq]
  · intro b _ hb
    exact Finset.sum_eq_zero fun l _ => by rw [Matrix.blockDiagonal'_apply_ne _ _ _ hb, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem blockDiag_mul_apply {n : ℕ} {κ : Type} (N : Matrix (Σ _ : Fin n, ι) κ ℂ) (Y : Matrix ι ι ℂ)
    (k : κ) (i : Fin n) (j : ι) :
    (Matrix.blockDiagonal' (fun _ : Fin n => Y) * N) ⟨i, j⟩ k = ∑ l, Y j l * N ⟨i, l⟩ k := by
  rw [Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single i]
  · exact Finset.sum_congr rfl fun l _ => by rw [Matrix.blockDiagonal'_apply_eq]
  · intro b _ hb
    exact Finset.sum_eq_zero fun l _ => by rw [Matrix.blockDiagonal'_apply_ne _ _ _ hb.symm, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

end Mat

end PrismTransfer

namespace PrismTransfer

section Maps

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]

def rowMap {n : ℕ} (c : K) (x : Fin n → V →ₗ[K] V) : (Fin n → V) →ₗ[K] V :=
  ∑ i, (c • x i) ∘ₗ LinearMap.proj i

def colMap {n : ℕ} (c : K) (x : Fin n → V →ₗ[K] V) : V →ₗ[K] (Fin n → V) :=
  LinearMap.pi fun i => c • x i

theorem rowMap_apply {n : ℕ} (c : K) (x : Fin n → V →ₗ[K] V) (a : Fin n → V) :
    rowMap c x a = ∑ i, c • x i (a i) := by
  simp [rowMap]

theorem colMap_apply {n : ℕ} (c : K) (x : Fin n → V →ₗ[K] V) (y : V) (i : Fin n) :
    colMap c x y i = c • x i y := by
  rfl

theorem toMatrix_rowMap {n : ℕ} (b : Basis ι K V) (c : K) (x : Fin n → V →ₗ[K] V) (k : ι)
    (i : Fin n) (j : ι) :
    LinearMap.toMatrix (Pi.basis fun _ : Fin n => b) b (rowMap c x) k ⟨i, j⟩ =
      c * LinearMap.toMatrix b b (x i) k j := by
  have h : rowMap c x ((Pi.basis fun _ : Fin n => b) ⟨i, j⟩) = c • x i (b j) := by
    rw [rowMap_apply, Finset.sum_eq_single i]
    · simp [Pi.basis_apply]
    · intro i' _ hi'
      simp [Pi.basis_apply, hi']
    · simp
  rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, h]
  simp

theorem toMatrix_colMap {n : ℕ} (b : Basis ι K V) (c : K) (x : Fin n → V →ₗ[K] V) (k : ι)
    (i : Fin n) (j : ι) :
    LinearMap.toMatrix b (Pi.basis fun _ : Fin n => b) (colMap c x) ⟨i, j⟩ k =
      c * LinearMap.toMatrix b b (x i) j k := by
  simp [LinearMap.toMatrix_apply, Pi.basis_repr, colMap_apply]

theorem opNormAt_rowMap {n : ℕ} (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (G : ℕ) (x : Fin n → V →ₗ[K] V) (v : InfinitePlace K)
    (hx : ∀ i, opNormAt b X b X v (x i) ≤ 1) :
    opNormAt (Pi.basis fun _ : Fin n => b) (fun v => Matrix.blockDiagonal' fun _ : Fin n => X v) b X v
      (rowMap ((G : K) ^ 3) x) ≤ (G : ℝ) ^ 3 * Real.sqrt n := by
  dsimp only [opNormAt]
  refine row_norm_le (fun i => (X v)⁻¹ * (LinearMap.toMatrix b b (x i)).map v.embedding * X v)
    ((G : ℝ) ^ 3) (by positivity) hx _ ?_
  intro k p
  obtain ⟨i, j⟩ := p
  dsimp only
  rw [mul_blockDiag_apply]
  simp only [Matrix.mul_apply, Matrix.map_apply, toMatrix_rowMap, map_mul, map_pow, map_natCast,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  push_cast
  ring

theorem opNormAt_colMap {n : ℕ} (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (G : ℕ) (x : Fin n → V →ₗ[K] V) (v : InfinitePlace K)
    (hx : ∀ i, opNormAt b X b X v (x i) ≤ 1) :
    opNormAt b X (Pi.basis fun _ : Fin n => b) (fun v => Matrix.blockDiagonal' fun _ : Fin n => X v) v
      (colMap ((G : K) ^ 3) x) ≤ (G : ℝ) ^ 3 * Real.sqrt n := by
  dsimp only [opNormAt]
  rw [blockDiag_inv (X v) (hX v)]
  refine col_norm_le (fun i => (X v)⁻¹ * (LinearMap.toMatrix b b (x i)).map v.embedding * X v)
    ((G : ℝ) ^ 3) (by positivity) hx _ ?_
  intro p k
  obtain ⟨i, j⟩ := p
  dsimp only
  conv_lhs => rw [Matrix.mul_apply]
  simp only [blockDiag_mul_apply]
  simp only [Matrix.mul_apply, Matrix.map_apply, toMatrix_colMap, map_mul, map_pow, map_natCast,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun m _ => ?_
  push_cast
  ring

variable {W κ : Type} [AddCommGroup W] [Module K W] [Fintype κ] [DecidableEq κ]

theorem htMap_le (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (b' : Basis κ K W)
    (X' : InfinitePlace K → Matrix κ κ ℂ) (φ : V →ₗ[K] W) (B : ℝ) (hB : 1 ≤ B)
    (h : ∀ v, opNormAt b X b' X' v φ ≤ B) : htMap b X b' X' φ ≤ 2 * Real.log B := by
  show (1 / (nPl K : ℝ)) * ∑ v, Real.log (opNormAt b X b' X' v φ ^ 2) ≤ 2 * Real.log B
  have hterm : ∀ v, Real.log (opNormAt b X b' X' v φ ^ 2) ≤ 2 * Real.log B := by
    intro v
    have hx0 : 0 ≤ opNormAt b X b' X' v φ := norm_nonneg _
    have h2 : Real.log (B ^ 2) = 2 * Real.log B := by
      rw [Real.log_pow]
      norm_num
    rw [← h2]
    rcases eq_or_lt_of_le (sq_nonneg (opNormAt b X b' X' v φ)) with h0 | h0
    · rw [← h0, Real.log_zero]
      exact Real.log_nonneg (by nlinarith)
    · exact Real.log_le_log h0 (by nlinarith [h v])
  rcases Nat.eq_zero_or_pos (nPl K) with h0 | hpos
  · rw [h0, Nat.cast_zero, div_zero, zero_mul]
    exact mul_nonneg zero_le_two (Real.log_nonneg hB)
  · have hn : (0 : ℝ) < nPl K := by exact_mod_cast hpos
    have hne : (nPl K : ℝ) ≠ 0 := hn.ne'
    calc (1 / (nPl K : ℝ)) * ∑ v, Real.log (opNormAt b X b' X' v φ ^ 2)
        ≤ (1 / (nPl K : ℝ)) * ∑ _v : InfinitePlace K, 2 * Real.log B := by
          gcongr with v _
          exact hterm v
      _ = 2 * Real.log B := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          have hc : (nPl K : ℝ) = (Fintype.card (InfinitePlace K) : ℝ) := rfl
          rw [← hc, one_div, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

theorem log_bound (G n : ℕ) (hG : 0 < G) (hn : 0 < n) :
    1 ≤ (G : ℝ) ^ 3 * Real.sqrt n ∧
      2 * Real.log ((G : ℝ) ^ 3 * Real.sqrt n) = 6 * Real.log G + Real.log n := by
  have hG1 : (1 : ℝ) ≤ G := by exact_mod_cast hG
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hG0 : (0 : ℝ) < G := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have h1 : (1 : ℝ) ≤ (G : ℝ) ^ 3 := one_le_pow₀ hG1
  have h2 : (1 : ℝ) ≤ Real.sqrt n := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hn1
  refine ⟨one_le_mul_of_one_le_of_one_le h1 h2, ?_⟩
  rw [Real.log_mul (pow_pos hG0 3).ne' (Real.sqrt_pos.mpr hn0).ne', Real.log_pow,
    Real.log_sqrt hn0.le]
  push_cast
  ring

end Maps

section Lat

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]

theorem pow_smul_eq (G : ℕ) (y : V) : ((G : 𝓞 K) ^ 3) • y = ((G : K) ^ 3) • y := by
  simp only [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]

theorem pow_ne_zero' (G : ℕ) (hG : 0 < G) : ((G : K) ^ 3) ≠ 0 := pow_ne_zero 3 (Nat.cast_ne_zero.mpr hG.ne')

theorem pi_ne_bot {n : ℕ} (hn : 0 < n) (A : Submodule (𝓞 K) V) (hA : A ≠ ⊥) :
    (Submodule.pi Set.univ fun _ : Fin n => A) ≠ ⊥ := by
  obtain ⟨x, hxA, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA
  intro h
  have hmem : (Pi.single (⟨0, hn⟩ : Fin n) x : Fin n → V) ∈
      Submodule.pi Set.univ (fun _ : Fin n => A) := by
    rw [Submodule.mem_pi]
    intro i _
    by_cases hi : i = ⟨0, hn⟩
    · subst hi
      simpa using hxA
    · simp [Pi.single_apply, hi]
  rw [h, Submodule.mem_bot] at hmem
  exact hx0 (by simpa using congrFun hmem ⟨0, hn⟩)

theorem colMap_injOn {n : ℕ} (G : ℕ) (hG : 0 < G) (xs : Fin n → V →ₗ[K] V) (B : Submodule (𝓞 K) V)
    (h : ∀ c ∈ B, (∀ i, xs i c = 0) → c = 0) :
    Set.InjOn (colMap ((G : K) ^ 3) xs) (B : Set V) := by
  intro y₁ hy₁ y₂ hy₂ hxy
  refine sub_eq_zero.mp (h _ (sub_mem hy₁ hy₂) fun i => ?_)
  have hi := congrFun hxy i
  rw [colMap_apply, colMap_apply] at hi
  rw [map_sub, sub_eq_zero]
  exact smul_right_injective V (pow_ne_zero 3 (Nat.cast_ne_zero.mpr hG.ne')) hi

theorem colMap_map_le {n : ℕ} (G : ℕ) (xs : Fin n → V →ₗ[K] V) (A B : Submodule (𝓞 K) V)
    (h : ∀ i, ∀ c ∈ B, ((G : 𝓞 K) ^ 3) • xs i c ∈ A) :
    B.map ((colMap ((G : K) ^ 3) xs).restrictScalars (𝓞 K)) ≤
      Submodule.pi Set.univ fun _ : Fin n => A := by
  intro y hy
  obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.mp hy
  rw [Submodule.mem_pi]
  intro i _
  change colMap ((G : K) ^ 3) xs c i ∈ A
  rw [colMap_apply, ← PrismTransfer.pow_smul_eq]
  exact h i c hc

theorem rowMap_injOn {n : ℕ} (G : ℕ) (hG : 0 < G) (x : Fin n → V →ₗ[K] V) (A : Submodule (𝓞 K) V)
    (h : ∀ a : Fin n → V, (∀ i, a i ∈ A) → ∑ i, x i (a i) = 0 → a = 0) :
    Set.InjOn (rowMap ((G : K) ^ 3) x) ((Submodule.pi Set.univ fun _ : Fin n => A : Submodule (𝓞 K) (Fin n → V)) : Set (Fin n → V)) := by
  intro a₁ ha₁ a₂ ha₂ hEq
  have hsub : a₁ - a₂ ∈ (Submodule.pi Set.univ fun _ : Fin n => A) := sub_mem ha₁ ha₂
  rw [Submodule.mem_pi] at hsub
  refine sub_eq_zero.mp (h _ (fun i => hsub i (Set.mem_univ i)) ?_)
  have h2 : rowMap ((G : K) ^ 3) x (a₁ - a₂) = 0 := by rw [map_sub, hEq, sub_self]
  rw [rowMap_apply, ← Finset.smul_sum] at h2
  exact (smul_eq_zero.mp h2).resolve_left (pow_ne_zero 3 (Nat.cast_ne_zero.mpr hG.ne'))

theorem rowMap_map_le {n : ℕ} (G : ℕ) (x : Fin n → V →ₗ[K] V) (A B : Submodule (𝓞 K) V)
    (h : ∀ i, ∀ a ∈ A, ((G : 𝓞 K) ^ 3) • x i a ∈ B) :
    (Submodule.pi Set.univ fun _ : Fin n => A).map
      ((rowMap ((G : K) ^ 3) x).restrictScalars (𝓞 K)) ≤ B := by
  intro y hy
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hy
  rw [Submodule.mem_pi] at ha
  change rowMap ((G : K) ^ 3) x a ∈ B
  rw [rowMap_apply]
  refine sum_mem fun i _ => ?_
  rw [← PrismTransfer.pow_smul_eq]
  exact h i (a i) (ha i (Set.mem_univ i))

end Lat

end PrismTransfer

open PrismTransfer

theorem transferPart_of (hMap : MapMu) (hPow : PowMu) : TransferPart := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX A B n G x xs hA hB hA0 hn hG hxA hxsB hx1 hxs1 hinj hinj' hrk
  obtain ⟨p1, p2, _⟩ := hPow K V ι b X hX A n hA hA0 hn
  have hXn : ∀ v, IsUnit (Matrix.blockDiagonal' fun _ : Fin n => X v).det :=
    fun v => blockDiag_det (X v) (hX v)
  have hAn : (Submodule.pi Set.univ fun _ : Fin n => A).FG := Submodule.fg_pi fun _ => hA
  have hAn0 := pi_ne_bot hn A hA0
  have hrA : rkK A ≠ 0 := Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.rkK_ne_zero b A hA0
  have hB0 : B ≠ ⊥ := by
    intro h
    rw [h, Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.rkK_bot] at hrk
    exact (Nat.mul_ne_zero hn.ne' hrA) hrk.symm
  obtain ⟨hb1, hb2⟩ := log_bound G n hG hn
  have d1 := hMap K (Fin n → V) (Σ _ : Fin n, ι) V ι (Pi.basis fun _ : Fin n => b)
    (fun v => Matrix.blockDiagonal' fun _ : Fin n => X v) b X hXn hX (rowMap ((G : K) ^ 3) x)
    (Submodule.pi Set.univ fun _ : Fin n => A) B hAn hB hAn0 (rowMap_injOn G hG x A hinj)
    (rowMap_map_le G x A B hxA) (by rw [hrk, p1])
  have d2 := hMap K V ι (Fin n → V) (Σ _ : Fin n, ι) b X (Pi.basis fun _ : Fin n => b)
    (fun v => Matrix.blockDiagonal' fun _ : Fin n => X v) hX hXn (colMap ((G : K) ^ 3) xs)
    B (Submodule.pi Set.univ fun _ : Fin n => A) hB hAn hB0 (colMap_injOn G hG xs B hinj')
    (colMap_map_le G xs A B hxsB) (by rw [hrk, p1])
  have e1 := htMap_le (Pi.basis fun _ : Fin n => b)
    (fun v => Matrix.blockDiagonal' fun _ : Fin n => X v) b X (rowMap ((G : K) ^ 3) x) _ hb1
    (fun v => opNormAt_rowMap b X G x v fun i => hx1 i v)
  have e2 := htMap_le b X (Pi.basis fun _ : Fin n => b)
    (fun v => Matrix.blockDiagonal' fun _ : Fin n => X v) (colMap ((G : K) ^ 3) xs) _ hb1
    (fun v => opNormAt_colMap b X hX G xs v fun i => hxs1 i v)
  rw [hb2] at e1 e2
  rw [p2] at d1 d2
  have h0 : degD b X B - (n : ℝ) * degD b X A =
      ((n : ℝ) * (rkK A : ℝ)) * (muDef b X B - muDef b X A) := by
    unfold degD
    rw [hrk]
    push_cast
    ring
  rw [h0, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) * (rkK A : ℝ)), mul_comm]
  refine mul_le_mul_of_nonneg_right (abs_le.2 ⟨by linarith, by linarith⟩) (by positivity)

theorem transferMuMax_of (hSc : ScaleSandwich) (hOrth : OrthSum) (hPow : PowMu) : TransferMuMax := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX S _ A B A0 C G n xs hA0 hC hA0ne hG hnG horth hBle hGmem hAC
    hxs hxs1 hinj
  have hG0 : (G : K) ≠ 0 := by exact_mod_cast hG.ne'
  have hBfg : ∀ s, (B s).FG := fun s => Submodule.FG.of_le hA0 (hBle s)
  have hsup0 : (⨆ s, B s) ≠ ⊥ := by
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA0ne
    intro h
    have h1 := hGmem a ha
    rw [h, Submodule.mem_bot, natCast_smul_eq] at h1
    exact ha0 ((smul_eq_zero.1 h1).resolve_left hG0)
  have s1 := (hSc K V ι b X hX A0 (⨆ s, B s) G hA0 hA0ne hG (iSup_le hBle) hGmem).2.2.2.2
  have hlG : 0 ≤ Real.log G := Real.log_natCast_nonneg G
  have s2 := (hOrth K V ι b X hX S B hBfg horth).2.2 (muMaxDef b X C + 13 / 2 * Real.log G)
    (fun s hs => by
      have hn : 0 < n s := by
        rcases Nat.eq_zero_or_pos (n s) with h0 | h0
        · exfalso
          apply hs
          rw [Submodule.eq_bot_iff]
          intro c hc
          refine hinj s c hc fun i => ?_
          exact absurd i.2 (by omega)
        · exact h0
      have hC0 : C ≠ ⊥ := by
        intro h
        apply hs
        rw [Submodule.eq_bot_iff]
        intro c hc
        refine hinj s c hc fun i => ?_
        have h1 := hAC s (hxs s i c hc)
        rw [h, Submodule.mem_bot, pow_smul_eq] at h1
        exact (smul_eq_zero.1 h1).resolve_left (pow_ne_zero' G hG)
      obtain ⟨_, _, p3⟩ := hPow K V ι b X hX C (n s) hC hC0 hn
      have hXn : ∀ v, IsUnit (Matrix.blockDiagonal' fun _ : Fin (n s) => X v).det :=
        fun v => blockDiag_det (X v) (hX v)
      have hCn : (Submodule.pi Set.univ fun _ : Fin (n s) => C).FG := Submodule.fg_pi fun _ => hC
      have hio := colMap_injOn G hG (xs s) (B s) (hinj s)
      have hne : (B s).map ((colMap ((G : K) ^ 3) (xs s)).restrictScalars (𝓞 K)) ≠ ⊥ := by
        obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hs
        intro h
        have h1 : colMap ((G : K) ^ 3) (xs s) c ∈
            (B s).map ((colMap ((G : K) ^ 3) (xs s)).restrictScalars (𝓞 K)) := ⟨c, hc, rfl⟩
        rw [h, Submodule.mem_bot] at h1
        exact hc0 (hio hc (B s).zero_mem (by rw [h1, map_zero]))
      have d := ((slope_inequality_mean K V ι (Fin (n s) → V) (Σ _ : Fin (n s), ι) b X
        (Pi.basis fun _ : Fin (n s) => b) (fun v => Matrix.blockDiagonal' fun _ : Fin (n s) => X v)
        hX hXn (colMap ((G : K) ^ 3) (xs s)) (B s) (hBfg s) hne).2
        (Submodule.pi Set.univ fun _ : Fin (n s) => C) hCn
        (colMap_map_le G (xs s) C (B s) fun i c hc => hAC s (hxs s i c hc))).2 hio
      obtain ⟨hb1, hb2⟩ := log_bound G (n s) hG hn
      have e := htMap_le b X (Pi.basis fun _ : Fin (n s) => b)
        (fun v => Matrix.blockDiagonal' fun _ : Fin (n s) => X v) (colMap ((G : K) ^ 3) (xs s)) _ hb1
        (fun v => opNormAt_colMap b X hX G (xs s) v fun i => hxs1 s i v)
      rw [hb2] at e
      rw [p3] at d
      have hl : 2 * Real.log (n s) ≤ Real.log G := by
        have h1 : Real.log (((n s : ℕ) : ℝ) ^ 2) ≤ Real.log G :=
          Real.log_le_log (by positivity) (by exact_mod_cast hnG s)
        rw [Real.log_pow] at h1
        exact_mod_cast h1
      linarith) hsup0
  linarith

end Formalism.BranchingDeterminantCap
