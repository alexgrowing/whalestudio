import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemInvLSIffTendsto
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerContentValuationDetPowBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinXiExtMemRigidTensorIffStatement
open PowerSeries GlobalTheory.BK Filter Topology

namespace GlobalTheory.BK

theorem norm_natCast_eq_rpow_padicValNat (l : ℕ) [Fact l.Prime] (K : Type) [NormedField K]
    [NormedAlgebra ℚ_[l] K] (N : ℕ) (hN : N ≠ 0) :
    ‖(N : K)‖ = (l : ℝ) ^ (-(padicValNat l N : ℝ)) := by
  rw [← map_natCast (algebraMap ℚ_[l] K), norm_algebraMap',
    Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hN), Padic.valuation_natCast,
    ← Real.rpow_intCast]
  congr 1
  push_cast
  simp [padicValRat.of_nat]

theorem wS_le_rpow (K : Type) [NormedField K] [IsUltrametricDist K] (l e : ℕ) [Fact l.Prime]
    [NormedAlgebra ℚ_[l] K] [NeZero e] (n : ℕ) :
    wS K e n ≤ (l : ℝ) ^ (1 / ((l : ℝ) - 1)) * ((n : ℝ) + 1) *
      (l : ℝ) ^ (-(n : ℝ) * (1 / ((e : ℝ) * ((l : ℝ) - 1)))) := by
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have hq : (0 : ℝ) < (l : ℝ) - 1 := by linarith
  have he : (0 : ℝ) < e := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne e)
  set m := n / e with hmdef
  have hv := GlobalTheory.DetPowContent.padicValNat_factorial_ge l (Fact.out : l.Prime) m
  have hm : (n : ℝ) / e - 1 ≤ m := by
    have h1 : n < (m + 1) * e := by
      have := Nat.lt_div_mul_add (a := n) (Nat.pos_of_ne_zero (NeZero.ne e))
      rw [hmdef]; linarith
    have h2 : (n : ℝ) < ((m : ℝ) + 1) * e := by exact_mod_cast h1
    rw [div_sub_one he.ne', div_le_iff₀ he]; linarith
  have hm1 : ((m : ℝ) + 1) ≤ (n : ℝ) + 1 := by
    have : m ≤ n := Nat.div_le_self n e
    exact_mod_cast Nat.add_le_add_right this 1
  unfold wS
  rw [← hmdef, norm_natCast_eq_rpow_padicValNat l K _ (Nat.factorial_ne_zero m)]
  have hexp : -(padicValNat l m.factorial : ℝ) ≤ Real.logb l ((m : ℝ) + 1) + 1 / ((l : ℝ) - 1) +
      -(n : ℝ) * (1 / ((e : ℝ) * ((l : ℝ) - 1))) := by
    have h3 : (n : ℝ) * (1 / ((e : ℝ) * ((l : ℝ) - 1))) = ((n : ℝ) / e) / ((l : ℝ) - 1) := by
      field_simp
    have h4 : ((n : ℝ) / e) / ((l : ℝ) - 1) ≤ (m : ℝ) / ((l : ℝ) - 1) + 1 / ((l : ℝ) - 1) := by
      rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) hq.le
    nlinarith
  calc (l : ℝ) ^ (-(padicValNat l m.factorial : ℝ))
      ≤ (l : ℝ) ^ (Real.logb l ((m : ℝ) + 1) + 1 / ((l : ℝ) - 1) +
          -(n : ℝ) * (1 / ((e : ℝ) * ((l : ℝ) - 1)))) := Real.rpow_le_rpow_of_exponent_le hl.le hexp
    _ = ((m : ℝ) + 1) * (l : ℝ) ^ (1 / ((l : ℝ) - 1)) *
          (l : ℝ) ^ (-(n : ℝ) * (1 / ((e : ℝ) * ((l : ℝ) - 1)))) := by
      rw [Real.rpow_add hl0, Real.rpow_add hl0, Real.rpow_logb hl0 hl.ne' (by positivity)]
    _ ≤ _ := by
      rw [mul_comm ((m : ℝ) + 1)]
      gcongr

end GlobalTheory.BK

open Matrix

namespace GlobalTheory.BK

theorem R_le_invL_S (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [Algebra O K] [IsUnitBall O K] (l e : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e]
    (k : ℝ) (hk : k < 1 / ((e : ℝ) * (l - 1))) : R O K l k ≤ invL l (S O K e) := by
  intro f hf
  rw [mem_invL_S_iff_tendsto O K l e f]
  have hR := mem_R.1 hf
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  set k0 := 1 / ((e : ℝ) * (l - 1)) with hk0
  set q := (l : ℝ) ^ (k - k0) with hqdef
  have hq0 : 0 ≤ q := Real.rpow_nonneg hl0.le _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg hl (by linarith)
  set C := (l : ℝ) ^ (1 / ((l : ℝ) - 1)) with hC
  have hg : Tendsto (fun n : ℕ => C * (((n : ℝ) + 1) * q ^ n)) atTop (𝓝 0) := by
    have h1 := (tendsto_self_mul_const_pow_of_lt_one hq0 hq1).add
      (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1)
    rw [add_zero] at h1
    have h2 := h1.const_mul C
    rw [mul_zero] at h2
    exact h2.congr fun n => by ring
  have hprod := hR.mul hg
  rw [zero_mul] at hprod
  refine squeeze_zero (fun n => mul_nonneg (norm_nonneg _) (wS_nonneg e n)) (fun n => ?_) hprod
  have hw := wS_le_rpow K l e n
  have hrad : rad l k ^ n * q ^ n = (l : ℝ) ^ (-(n : ℝ) * k0) := by
    rw [rad, hqdef, ← Real.rpow_mul_natCast hl0.le, ← Real.rpow_mul_natCast hl0.le,
      ← Real.rpow_add hl0]
    congr 1; ring
  calc ‖coeff n f‖ * wS K e n ≤ ‖coeff n f‖ * (C * ((n : ℝ) + 1) * (l : ℝ) ^ (-(n : ℝ) * k0)) :=
        mul_le_mul_of_nonneg_left hw (norm_nonneg _)
    _ = ‖coeff n f‖ * rad l k ^ n * (C * (((n : ℝ) + 1) * q ^ n)) := by
        rw [← hrad]; ring

theorem mulVec_mem_vecs {ι : Type} [Fintype ι] {O K : Type} [CommRing O] [NormedField K] [Algebra O K]
    {B : Subalgebra O K⟦X⟧} {M : Matrix ι ι K⟦X⟧} (hM : ∀ i j, M i j ∈ B) {v : ι → K⟦X⟧}
    (hv : v ∈ vecs ι B) : M *ᵥ v ∈ vecs ι B := fun i =>
  Subalgebra.sum_mem _ fun j _ => B.mul_mem (hM i j) (hv j)

end GlobalTheory.BK

open GlobalTheory.BK in
theorem GlobalTheory.BK.xi_trivialises_invL_S : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] (P : PhiMod O K l e a ι), (∀ k : ℝ, k < 1 / ((e : ℝ) * (l - 1)) → R O K l k ≤ invL l (S O K e)) ∧ ∀ w : Vec K a ι, P.xiExt w ∈ P.MMl ↔ w ∈ P.Mext (invL l (S O K e)) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ P
  refine ⟨fun k hk => R_le_invL_S O K l e k hk, fun w => ?_⟩
  have hl : (2 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).two_le
  have he : (0 : ℝ) < e := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne e)
  set k : ℝ := (1 / ((e : ℝ) * l) + 1 / ((e : ℝ) * (l - 1))) / 2 with hkdef
  have hlt : 1 / ((e : ℝ) * l) < 1 / ((e : ℝ) * (l - 1)) :=
    one_div_lt_one_div_of_lt (by nlinarith) (by nlinarith)
  have hk1 : 1 / ((e : ℝ) * l) < k := by rw [hkdef]; linarith
  have hk2 : k < 1 / ((e : ℝ) * (l - 1)) := by rw [hkdef]; linarith
  have hRB := R_le_invL_S O K l e k hk2
  have hT := GlobalTheory.T.breuilKisin_xiExt_mem_rigidTensor_iff O K l e a ι P k hk1
  set Y : ZMod a → Matrix ι ι K⟦X⟧ := fun τ => P.mxInv τ * P.xiMat τ with hY
  have hext : ∀ (B : Subalgebra O K⟦X⟧) (v : Vec K a ι),
      P.xiExt v ∈ P.ext B ↔ ∀ τ, Y τ *ᵥ v τ ∈ vecs ι B := by
    intro B v
    simp only [PhiMod.ext, mem_tot, PhiMod.mem_extc_iff, PhiMod.xiExt_apply, Matrix.mulVec_mulVec, hY]
  have hM : ∀ (B : Subalgebra O K⟦X⟧) (v : Vec K a ι), v ∈ P.Mext B ↔ ∀ τ, v τ ∈ vecs ι B := by
    intro B v
    simp only [PhiMod.Mext, mem_tot]
  have hYu : ∀ τ, IsUnit (Y τ).det := by
    intro τ
    rw [hY, Matrix.det_mul]
    exact (Matrix.isUnit_det_of_left_inverse (P.mx_mul_mxInv τ)).mul (P.isUnit_det_xiMat τ)

  have hYR : ∀ τ i j, Y τ i j ∈ R O K l k := by
    intro τ i j
    have h0 : (fun _ : ZMod a => (Pi.single j 1 : ι → K⟦X⟧)) ∈ P.Mext (R O K l k) := by
      rw [hM]; intro τ' i'
      rw [Pi.single_apply]; split_ifs
      exacts [one_mem _, zero_mem _]
    have h1 := (hext _ _).1 ((hT _).2 h0) τ i
    simpa [Matrix.mulVec_single_one] using h1

  have hZR : ∀ τ i j, (Y τ)⁻¹ i j ∈ R O K l k := by
    intro τ i j
    have h0 : P.xiExt (fun τ' => (Y τ')⁻¹ *ᵥ (Pi.single j 1 : ι → K⟦X⟧)) ∈ P.Lk k := by
      rw [PhiMod.Lk, hext]; intro τ' i'
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hYu τ'), Matrix.one_mulVec, Pi.single_apply]
      split_ifs
      exacts [one_mem _, zero_mem _]
    have h1 := (hM _ _).1 ((hT _).1 h0) τ i
    simpa [Matrix.mulVec_single_one] using h1
  rw [PhiMod.MMl, hext, hM]
  constructor
  · intro h τ
    have := mulVec_mem_vecs (fun i j => hRB (hZR τ i j)) (h τ)
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (hYu τ), Matrix.one_mulVec] at this
  · intro h τ
    exact mulVec_mem_vecs (fun i j => hRB (hYR τ i j)) (h τ)
