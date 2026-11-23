import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImagePolynomialAction

noncomputable section

namespace GlobalTheory.Proof.eulerE_add_smul_mem_eisenstein_shift_graded

open PowerSeries GlobalTheory.BK

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
  {η H : ℕ}

omit [CompleteSpace K] in

theorem conn_mem_ext_Rpi (D : BKDat O K l e a ι η H) {y : Vec K a ι}
    (hy : y ∈ D.ext (Rpi O K l e)) : D.conn y ∈ D.ext (Rpi O K l e) := by
  have hf : ∀ i τ, (Matrix.mulVec (D.mxInv τ) (y τ)) i ∈ Rpi O K l e := fun i τ =>
    D.mem_extc_iff.1 (mem_tot.1 hy τ) i
  rw [D.eq_sum_phi_bas y, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  have hL : D.phi (bas i) ∈ D.L := D.phi_mem_L (D.bas_mem_M i)
  have hM : D.phi (bas i) ∈ D.MM := D.ext_mono (A_le_S l e) hL
  rw [PhiMod.conn_smul_tot]
  refine Submodule.add_mem _ ?_ ?_
  · exact D.smul_tot_mem_ext (fun τ => N_mem (derivative_mem_R l (hf i τ)))
      (D.ext_mono (S_le_R l e) hM)
  · exact D.smul_tot_mem_ext (hf i) (D.ext_mono (S_le_R l e) (D.conn_mem_MM hM))

omit [CompleteSpace K] in
theorem EN_add_smul_mem_shiftE' (D : BKDat O K l e a ι η H) (j : ℤ) (x : Vec K a ι)
    (hx : x ∈ shiftE l e j (D.ext (Rpi O K l e))) :
    D.EN x + ((j * e * l : ℤ) : K) • x ∈ shiftE l e (j + 1) (D.ext (Rpi O K l e)) := by
  rw [mem_shiftE] at hx ⊢
  set y := Ezpow K l e (-j) • x with hy
  have hxy : x = Ezpow K l e j • y := by
    rw [hy, smul_smul, mul_comm, Ezpow_neg_mul, one_smul]
  clear_value y
  clear hy
  have h1 : Ezpow K l e (j + 1) = Ezpow K l e j * E K l e := by
    rw [Ezpow_add, show Ezpow K l e 1 = E K l e from (Ezpow_natCast l e 1).trans (pow_one _)]
  have hc : ((j * e * l : ℤ) : K) • x = ((j * e * l : ℤ) : K⟦X⟧) • x := by
    rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]
  have hN : E K l e * N K (Ezpow K l e j) + ((j * e * l : ℤ) : K⟦X⟧) * Ezpow K l e j =
      Ezpow K l e (j + 1) * ((j * e : ℤ) : K⟦X⟧) := by
    rw [E_mul_N_Ezpow, N_E, h1, E]
    push_cast
    ring
  have key : D.EN x + ((j * e * l : ℤ) : K) • x =
      Ezpow K l e (j + 1) • ((j * e : ℤ) • y + D.conn y) := by
    rw [hc, PhiMod.EN_apply, hxy, PhiMod.conn_smul, smul_add, smul_add, smul_smul, smul_smul, smul_smul,
      ← Int.cast_smul_eq_zsmul K⟦X⟧ (j * e : ℤ), smul_smul, ← hN, add_smul, h1, mul_comm (E K l e) (Ezpow K l e j)]
    abel
  rw [key, smul_smul, Ezpow_neg_mul, one_smul]
  exact Submodule.add_mem _ (zsmul_mem hx _) (conn_mem_ext_Rpi D hx)

theorem EN_add_smul_mem_shiftE :
    ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H) (j : ℤ) (x : Vec K a ι), x ∈ shiftE l e j (D.ext (Rpi O K l e)) → D.EN x + ((j * e * l : ℤ) : K) • x ∈ shiftE l e (j + 1) (D.ext (Rpi O K l e)) := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D j x hx
  exact EN_add_smul_mem_shiftE' D j x hx

end GlobalTheory.Proof.eulerE_add_smul_mem_eisenstein_shift_graded
