import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImagePolynomialAction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinIntegralityComputationStatement

noncomputable section

open PowerSeries GlobalTheory.BK

namespace GlobalTheory.Proof.breuilKisin_descent_operator_preserves_lattice

theorem integral : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), η < H → 10 * H + 2 ≤ l → GlobalTheory.IndefiniteRowSideFullHecke.ImagePolynomialAction.Integral D := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D hηH hl
  obtain ⟨-, hfil, hcomp⟩ := GlobalTheory.T.breuilKisin_integrality_computation O K l e a ι η H D hηH hl
  intro w hw
  obtain ⟨⟨y, hyM, rfl⟩, hinv⟩ := (D.desc.mem_Z).1 hw
  obtain ⟨p, hp, f, hf, hEq⟩ := hcomp y hyM
  have hfM := hfil f hf
  have h1 : E K l e ^ (2 * H) * Ezpow K l e (-(2 * H : ℤ)) = 1 := by
    simpa using E_pow_mul_Ezpow_neg (K := K) l e (2 * H)
  have hsplit : D.EN y = Ezpow K l e (-(2 * H : ℤ)) • p + Ezpow K l e (-(2 * H : ℤ)) • f := by
    rw [← smul_add, ← hEq, smul_smul, mul_comm, h1, one_smul]
  have hENy : D.EN y ∈ divE l e η D.Man := D.EN_mem_divE (D.M_le_Man hyM)
  have hy' : Ezpow K l e (-(2 * H : ℤ)) • p ∈ D.EM η := by
    have hA : E K l e ^ η • Ezpow K l e (-(2 * H : ℤ)) • p ∈ D.EM (2 * H) := by
      show E K l e ^ (2 * H) • E K l e ^ η • Ezpow K l e (-(2 * H : ℤ)) • p ∈ D.M
      rw [smul_comm (E K l e ^ (2 * H)) (E K l e ^ η), smul_smul (E K l e ^ (2 * H)), h1, one_smul]
      exact D.upper p hp
    have hB : E K l e ^ η • Ezpow K l e (-(2 * H : ℤ)) • p ∈ D.Man := by
      have : Ezpow K l e (-(2 * H : ℤ)) • p = D.EN y - Ezpow K l e (-(2 * H : ℤ)) • f := by
        rw [hsplit, add_sub_cancel_right]
      rw [this, smul_sub]
      exact sub_mem hENy (D.smul_mem_Man (pow_mem (E_mem l e _) η) hfM)
    exact D.mem_M_of_mem_Man hA hB
  refine (D.desc.mem_Z).2 ⟨⟨_, hy', ?_⟩, fun g => ?_⟩
  · rw [BKDat.Lc_cls, hsplit, map_add, add_eq_left.2 ((D.cls_eq_zero_iff).2 hfM)]
  · rw [D.actPol_Lc, hinv g]

end GlobalTheory.Proof.breuilKisin_descent_operator_preserves_lattice
