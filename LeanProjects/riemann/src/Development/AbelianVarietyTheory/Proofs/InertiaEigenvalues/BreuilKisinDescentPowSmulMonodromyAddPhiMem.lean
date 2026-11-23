import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsAlgebraMapEqRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDescentOperatorPreservesLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinIntegralityComputationStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinZetaFineBoundSecondBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowSmulDescentPhiMemLatticeOfOrbitBoundStatement

open PowerSeries GlobalTheory.BK

namespace GlobalTheory.BK.MonIntegral

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
  [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
  {η H : ℕ} (D : BKDat O K l e a ι η H)

omit [CompleteSpace K] in
theorem pow_smul_mem (W : Submodule O D.Pol) (n : ℕ) {w : D.Pol} (hw : w ∈ W) : (l : K) ^ n • w ∈ W := by
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  exact nsmul_mem hw _

omit [CompleteSpace K] [NeZero e] in

theorem E_smul_mem_EM {p : Vec K a ι} (hp : p ∈ D.L) : E K l e • p ∈ D.EM η := by
  rw [mem_divE, smul_comm]
  exact D.M.smul_mem (EIn l e (A O K)) (D.upper p hp)

omit [CompleteSpace K] in

theorem cls_E_smul_eq_zero {f : Vec K a ι} (hf : Ezpow K l e (-(2 * H : ℤ)) • f ∈ D.Man) :
    D.cls (E K l e • f) = 0 := by
  have h := D.smul_mem_Man (pow_mem (E_mem l e (Rpi O K l e)) (2 * H + 1)) hf
  have h1 : E K l e ^ (2 * H) * Ezpow K l e (-(2 * H : ℤ)) = 1 := by
    simpa using E_pow_mul_Ezpow_neg (K := K) l e (2 * H)
  rw [smul_smul, pow_succ', mul_assoc, h1, mul_one] at h
  exact D.cls_eq_zero_iff.2 h

end GlobalTheory.BK.MonIntegral

open GlobalTheory.BK.MonIntegral in

theorem GlobalTheory.BK.pow_smul_Mon_add_phi_mem_Z : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H), 1 ≤ η → η < H → 14 * H < l → 10 * H + 2 ≤ l → ∀ r : ℕ, 1 ≤ r → (∀ τ, ∀ c ∈ D.desc.chars τ, frobPeriod l c ≤ r) → (r + 2) * η < l + 1 → l ≠ 2 → ∀ y ∈ D.Y', ∀ m ∈ D.Minv, (l : K) ^ (η * (r + 1)) • D.Mon (y + D.phi m) ∈ D.Z := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D hη hH h14 h10 r hr hc hrl hl y hy m hm
  obtain ⟨hsplit, hfil, -⟩ := GlobalTheory.T.breuilKisin_integrality_computation O K l e a ι η H D hH h10
  have hint := GlobalTheory.T.breuilKisin_descent_operator_preserves_lattice O K l e a ι η H D hH h10
  have hyY : y ∈ D.Y := D.desc.Y'_le_Y η hy
  set W : Submodule O D.Pol :=
    ((D.EM η).restrictScalars O).map (D.cls.restrictScalars O) with hW
  have hL : ∀ p ∈ D.L, D.cls (E K l e • p) ∈ W := fun p hp => ⟨_, E_smul_mem_EM D hp, rfl⟩
  have hMM : ∀ μ ∈ D.MM, D.cls (E K l e • μ) ∈ W := fun μ hμ => by
    obtain ⟨p, hp, f, hf, rfl⟩ := hsplit μ hμ
    rw [smul_add, map_add, cls_E_smul_eq_zero D (hfil f hf), add_zero]
    exact hL p hp
  have h1 : D.Mon y ∈ W := by
    rw [D.Mon_eq]
    refine sub_mem (hint _ (D.desc.cls_mem_Z hyY)).1 ?_
    obtain ⟨p, hp, f, hf, h⟩ := GlobalTheory.T.breuilKisin_zeta_fine_bound_second_basis O K l e a ι η H D hη hH h14 y hy
    rw [h, smul_add, map_add, smul_comm (E K l e) _ p, smul_comm (E K l e) _ f,
      D.cls.map_smul ((l : K) ^ _), D.cls.map_smul (_⁻¹ : K), cls_E_smul_eq_zero D (hfil f hf), smul_zero, add_zero]
    exact pow_smul_mem D W _ (hL p hp)
  have h2 : (l : K) ^ (η * (r + 1)) • D.Mon (D.phi m) ∈ W := by
    rw [D.Mon_eq, smul_sub, BKDat.Lc_cls, PhiMod.EN_apply]
    refine sub_mem (pow_smul_mem D W _ (hMM _ (D.conn_mem_MM
      (D.ext_mono (A_le_S l e) (D.phi_mem_L hm.1))))) ?_
    rw [← map_smul, ← smul_comm (E K l e)]
    exact hMM _ (GlobalTheory.T.prime_pow_smul_descent_phi_mem_lattice_of_orbit_bound O K l e a ι η H D r hr hc hrl hl m hm)
  refine ⟨?_, ?_⟩
  · rw [map_add, smul_add]
    exact add_mem (pow_smul_mem D W _ h1) h2
  · refine D.desc.actPol.invariants.smul_mem _ (D.desc.Mon_mem_invariants (add_mem hyY.2 fun g => ?_))
    rw [D.desc.act_phi, hm.2 g]
