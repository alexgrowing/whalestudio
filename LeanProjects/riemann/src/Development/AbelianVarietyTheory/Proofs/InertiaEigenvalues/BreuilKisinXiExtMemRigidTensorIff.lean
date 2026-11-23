import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusMemRigidFunctionsOfMemInvertEisensteinStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRigidFunctionsClosedDiscOfAdicLimitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TendstoConstPowMulPowPowZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusRecursionDifferencesDecayGaussNormStatement

open PowerSeries GlobalTheory.BK Filter Topology

namespace GlobalTheory.BK.XiTriv
theorem frobA : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] (k : ℝ), 1 / ((e : ℝ) * l) < k → ∀ f ∈ invE l e (A O K), frob K l f ∈ R O K l k := GlobalTheory.T.frobenius_mem_rigidFunctions_of_mem_invertEisenstein
theorem limR : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l : ℕ) (k : ℝ) (f : K⟦X⟧) (s : ℕ → K⟦X⟧), (∀ n, s n ∈ R O K l k) → (∀ n, (X : K⟦X⟧) ^ (n + 1) ∣ f - s n) → Tendsto (fun n => normR l k (s (n + 1) - s n)) atTop (𝓝 0) → f ∈ R O K l k := GlobalTheory.T.mem_rigidFunctionsClosedDisc_of_adic_limit
theorem growth : ∀ (C r : ℝ) (l : ℕ), 0 ≤ C → 0 ≤ r → r < 1 → 2 ≤ l → Tendsto (fun n : ℕ => C ^ n * r ^ (l ^ n)) atTop (𝓝 0) := GlobalTheory.T.tendsto_const_pow_mul_pow_pow_zero'
theorem decay : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l a : ℕ) [Fact l.Prime] [NeZero a] (ι : Type) [Fintype ι] [DecidableEq ι] (k : ℝ), 0 < k → ∀ (B : ZMod a → Matrix ι ι K⟦X⟧) (c : ZMod a → Matrix ι ι K) (Z : ℕ → ZMod a → Matrix ι ι K⟦X⟧), (∀ τ i j, B τ i j ∈ R O K l k) → (∀ τ, Z 0 τ = (c τ).map C) → (∀ n τ, Z (n + 1) τ = B τ * (Z n (τ - 1)).map (frob K l) * (c τ).map C) → (∀ τ i j, (X : K⟦X⟧) ∣ Z 1 τ i j - Z 0 τ i j) → ∃ M β : ℝ, 0 ≤ β ∧ ∀ n τ i j, Z n τ i j ∈ R O K l k ∧ normR l k (Z (n + 1) τ i j - Z n τ i j) ≤ M * β ^ n * rad l k ^ (l ^ n) := GlobalTheory.T.frobenius_recursion_differences_decay_gaussNorm

theorem convB : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (l a : ℕ) [Fact l.Prime] [NeZero a] (ι : Type) [Fintype ι] [DecidableEq ι] (k : ℝ), 0 < k → ∀ (B : ZMod a → Matrix ι ι K⟦X⟧) (c : ZMod a → Matrix ι ι K) (Z : ℕ → ZMod a → Matrix ι ι K⟦X⟧) (Y : ZMod a → Matrix ι ι K⟦X⟧), (∀ τ i j, B τ i j ∈ R O K l k) → (∀ τ, Z 0 τ = (c τ).map C) → (∀ n τ, Z (n + 1) τ = B τ * (Z n (τ - 1)).map (frob K l) * (c τ).map C) → (∀ n τ i j, (X : K⟦X⟧) ^ (n + 1) ∣ Y τ i j - Z n τ i j) → ∀ τ i j, Y τ i j ∈ R O K l k := by
  intro O K _ _ _ _ _ l a _ _ ι _ _ k hk B c Z Y hB h0 hs hY τ i j
  have h1 : ∀ τ i j, (X : K⟦X⟧) ∣ Z 1 τ i j - Z 0 τ i j := fun τ i j => by
    have a1 := hY 0 τ i j
    have a2 := (pow_dvd_pow (X : K⟦X⟧) (by omega : 1 ≤ 2)).trans (hY 1 τ i j)
    rw [pow_one] at a1 a2
    have := dvd_sub a1 a2
    rwa [sub_sub_sub_cancel_left] at this
  obtain ⟨M, β, hβ, hD⟩ := decay O K l a ι k hk B c Z hB h0 hs h1
  have hr0 : 0 ≤ rad l k := rad_nonneg l k
  have hr1 : rad l k < 1 := rad_lt_one l hk
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  refine limR O K l k (Y τ i j) (fun n => Z n τ i j) (fun n => (hD n τ i j).1) (fun n => hY n τ i j) ?_
  have hg := (growth β (rad l k) l hβ hr0 hr1 hl2).const_mul M
  rw [mul_zero] at hg
  refine squeeze_zero (fun n => ?_) (fun n => ?_) hg
  · have hm := sub_mem (hD (n + 1) τ i j).1 (hD n τ i j).1
    exact (mul_nonneg (norm_nonneg _) (pow_nonneg hr0 0)).trans (le_normR hm 0)
  · rw [← mul_assoc]; exact (hD n τ i j).2
end GlobalTheory.BK.XiTriv

noncomputable section

namespace GlobalTheory.BK.XiTriv

open PowerSeries Matrix

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]

theorem frob_map_mul (M N : Matrix ι ι K⟦X⟧) :
    (M * N).map (frob K l) = M.map (frob K l) * N.map (frob K l) :=
  Matrix.map_mul (f := (frob K l).toRingHom)

theorem frob_map_one : (1 : Matrix ι ι K⟦X⟧).map (frob K l) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem dvd_mul_mul_apply {c : K⟦X⟧} (M D N : Matrix ι ι K⟦X⟧) (h : ∀ i j, c ∣ D i j) (i j : ι) :
    c ∣ (M * D * N) i j := by
  rw [Matrix.mul_apply]
  refine Finset.dvd_sum fun k _ => Dvd.dvd.mul_right ?_ _
  rw [Matrix.mul_apply]
  exact Finset.dvd_sum fun m _ => (h m k).mul_left _

namespace Seq

variable (P : PhiMod O K l e a ι)

def Ws (n : ℕ) : ZMod a → Matrix ι ι K⟦X⟧ :=
  (fun W τ => (P.mx0 τ).map C * (W (τ - 1)).map (frob K l) * P.mxInv τ)^[n] fun _ => 1

theorem Ws_zero (τ : ZMod a) : Ws P 0 τ = 1 := rfl

theorem Ws_succ (n : ℕ) (τ : ZMod a) : Ws P (n + 1) τ =
    (P.mx0 τ).map C * (Ws P n (τ - 1)).map (frob K l) * P.mxInv τ := by
  rw [Ws, Function.iterate_succ_apply']
  rfl

theorem Ws_mul (n : ℕ) (τ : ZMod a) : Ws P n τ * P.xiSeq n τ = 1 := by
  induction n generalizing τ with
  | zero => rw [Ws_zero, PhiMod.xiSeq_zero, Matrix.one_mul]
  | succ n ih =>
    have h1 := P.mxInv_mul_mx τ
    have h3 : (P.mx0 τ).map C * ((P.mxInv τ).map constantCoeff).map C = 1 := by
      rw [← Matrix.map_mul, P.matrix_mul_inv_const_eq_one τ, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [PhiMod.xiSeq_succ, Ws_succ]
    calc _ = (P.mx0 τ).map C * (Ws P n (τ - 1)).map (frob K l) * (P.mxInv τ * P.mx τ) *
          (P.xiSeq n (τ - 1)).map (frob K l) * ((P.mxInv τ).map constantCoeff).map C := by
          simp only [Matrix.mul_assoc]
      _ = (P.mx0 τ).map C * ((Ws P n (τ - 1) * P.xiSeq n (τ - 1)).map (frob K l)) *
          ((P.mxInv τ).map constantCoeff).map C := by
          rw [h1, frob_map_mul]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = 1 := by rw [ih, frob_map_one, Matrix.mul_one, h3]

theorem xiMat_mul_inv (τ : ZMod a) : P.xiMat τ * (P.xiMat τ)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (P.isUnit_det_xiMat τ)

theorem inv_sub_dvd (n : ℕ) (τ : ZMod a) (i j : ι) :
    (X : K⟦X⟧) ^ (n + 2) ∣ ((P.xiMat τ)⁻¹ - Ws P (n + 1) τ) i j := by
  have h : (P.xiMat τ)⁻¹ - Ws P (n + 1) τ =
      Ws P (n + 1) τ * (P.xiSeq (n + 1) τ - P.xiMat τ) * (P.xiMat τ)⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Ws_mul, Matrix.one_mul, Matrix.mul_assoc,
      xiMat_mul_inv, Matrix.mul_one]
  rw [h]
  refine dvd_mul_mul_apply _ _ _ (fun i j => ?_) i j
  rw [Matrix.sub_apply, ← neg_sub]
  exact (dvd_neg).2 (P.xiMat_sub_dvd (n + 1) τ i j)

end Seq

variable [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a]

theorem mulVec_mem {B : Subalgebra O K⟦X⟧} {M : Matrix ι ι K⟦X⟧} (hM : ∀ i j, M i j ∈ B)
    {v : ι → K⟦X⟧} (hv : v ∈ vecs ι B) : M *ᵥ v ∈ vecs ι B := fun i => by
  simp only [Matrix.mulVec, dotProduct]
  exact Subalgebra.sum_mem _ fun j _ => mul_mem (hM i j) (hv j)

theorem Y_mem (P : PhiMod O K l e a ι) {k : ℝ} (hk : 1 / ((e : ℝ) * l) < k) (τ : ZMod a) (i j : ι) :
    (P.mxInv τ * P.xiMat τ) i j ∈ R O K l k := by
  have hk0 : 0 < k := by
    have h1 := NeZero.pos e
    have h2 := (Fact.out : l.Prime).pos
    exact lt_trans (by positivity) hk
  refine convB O K l a ι k hk0 (fun τ => (P.mx (τ - 1)).map (frob K l))
    (fun τ => (P.mxInv τ).map constantCoeff) (fun n τ => P.mxInv τ * P.xiSeq (n + 1) τ)
    (fun τ => P.mxInv τ * P.xiMat τ) (fun τ i j => frobA O K l e k hk _ (P.mx_mem _ i j))
    (fun τ => ?_) (fun n τ => ?_) (fun n τ i j => ?_) τ i j
  · rw [PhiMod.xiSeq_succ, PhiMod.xiSeq_zero, frob_map_one, Matrix.mul_one, ← Matrix.mul_assoc,
      PhiMod.mxInv_mul_mx, Matrix.one_mul]
  · rw [PhiMod.xiSeq_succ P (n + 1), ← frob_map_mul, ← Matrix.mul_assoc (P.mx (τ - 1)),
      PhiMod.mx_mul_mxInv, Matrix.one_mul, ← Matrix.mul_assoc (P.mxInv τ), ← Matrix.mul_assoc (P.mxInv τ),
      PhiMod.mxInv_mul_mx, Matrix.one_mul]
  · have h : P.mxInv τ * P.xiMat τ - P.mxInv τ * P.xiSeq (n + 1) τ =
        P.mxInv τ * (P.xiMat τ - P.xiSeq (n + 1) τ) * 1 := by
      rw [Matrix.mul_one, Matrix.mul_sub]
    rw [← Matrix.sub_apply, h]
    exact dvd_mul_mul_apply _ _ _ (fun i j => (pow_dvd_pow _ (by omega)).trans
      (P.xiMat_sub_dvd (n + 1) τ i j)) i j

theorem Yi_mem (P : PhiMod O K l e a ι) {k : ℝ} (hk : 1 / ((e : ℝ) * l) < k) (τ : ZMod a) (i j : ι) :
    ((P.xiMat τ)⁻¹ * P.mx τ) i j ∈ R O K l k := by
  have hk0 : 0 < k := by
    have h1 := NeZero.pos e
    have h2 := (Fact.out : l.Prime).pos
    exact lt_trans (by positivity) hk
  have key := convB O K l a ι k hk0 (fun τ => ((P.mxInv (τ - 1)).map (frob K l))ᵀ)
    (fun τ => (P.mx0 τ)ᵀ) (fun n τ => (Seq.Ws P (n + 1) τ * P.mx τ)ᵀ)
    (fun τ => ((P.xiMat τ)⁻¹ * P.mx τ)ᵀ) (fun τ i j => frobA O K l e k hk _ (P.mxInv_mem _ j i))
    (fun τ => ?_) (fun n τ => ?_) (fun n τ i j => ?_) τ j i
  · simpa using key
  · show (Seq.Ws P (0 + 1) τ * P.mx τ)ᵀ = ((P.mx0 τ)ᵀ).map C
    rw [Seq.Ws_succ, Seq.Ws_zero, frob_map_one, Matrix.mul_one, Matrix.mul_assoc,
      PhiMod.mxInv_mul_mx, Matrix.mul_one, Matrix.transpose_map]
  · show (Seq.Ws P (n + 2) τ * P.mx τ)ᵀ = ((P.mxInv (τ - 1)).map (frob K l))ᵀ *
        ((Seq.Ws P (n + 1) (τ - 1) * P.mx (τ - 1))ᵀ).map (frob K l) * ((P.mx0 τ)ᵀ).map C
    rw [Matrix.transpose_map, Matrix.transpose_map, ← Matrix.transpose_mul,
      ← Matrix.transpose_mul]
    congr 1
    rw [Seq.Ws_succ P (n + 1), Matrix.mul_assoc _ (P.mxInv τ), PhiMod.mxInv_mul_mx, Matrix.mul_one,
      ← frob_map_mul,
      Matrix.mul_assoc (Seq.Ws P (n + 1) (τ - 1)), PhiMod.mx_mul_mxInv, Matrix.mul_one]
  · rw [Matrix.transpose_apply, Matrix.transpose_apply, ← Matrix.sub_apply, ← Matrix.sub_mul,
      ← Matrix.one_mul ((P.xiMat τ)⁻¹ - Seq.Ws P (n + 1) τ)]
    exact dvd_mul_mul_apply _ _ _ (fun i j => (pow_dvd_pow _ (by omega)).trans
      (Seq.inv_sub_dvd P n τ i j)) j i

end GlobalTheory.BK.XiTriv

end

open PowerSeries GlobalTheory.BK in
theorem GlobalTheory.BK.xiExt_mem_Lk_iff : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι) (k : ℝ), 1 / ((e : ℝ) * l) < k → ∀ w : Vec K a ι, P.xiExt w ∈ P.Lk k ↔ w ∈ P.Mext (R O K l k) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ P k hk w
  have hprod (τ : ZMod a) : ((P.xiMat τ)⁻¹ * P.mx τ) * (P.mxInv τ * P.xiMat τ) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (P.mx τ), PhiMod.mx_mul_mxInv, Matrix.one_mul,
      Matrix.nonsing_inv_mul _ (P.isUnit_det_xiMat τ)]
  constructor
  · intro h
    refine mem_tot.2 fun τ => ?_
    have h1 := P.mem_extc_iff.1 (mem_tot.1 h τ)
    rw [PhiMod.xiExt_apply, Matrix.mulVec_mulVec] at h1
    have h2 := XiTriv.mulVec_mem (XiTriv.Yi_mem P hk τ) h1
    rwa [Matrix.mulVec_mulVec, hprod, Matrix.one_mulVec] at h2
  · intro h
    refine mem_tot.2 fun τ => P.mem_extc_iff.2 ?_
    rw [PhiMod.xiExt_apply, Matrix.mulVec_mulVec]
    exact XiTriv.mulVec_mem (XiTriv.Y_mem P hk τ) (mem_tot.1 h τ)
