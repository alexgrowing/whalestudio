import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SgC
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelUnitInTowerSlActionRowVectorStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmoothedSiegelUnitIndexAddIntVectorStatement
open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg

namespace GlobalTheory.KZ

theorem act_sub_int_of_Gamma (x : Fin 2 → ℚ) (M : ℕ) (hM : 0 < M)
    (hx : ∃ a b : ℤ, x 0 = a / M ∧ x 1 = b / M) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma M) :
    ∃ n : Fin 2 → ℤ, act x γ = fun i => x i + n i := by
  obtain ⟨a, b, ha, hb⟩ := hx
  obtain ⟨h00, h01, h10, h11⟩ := CongruenceSubgroup.Gamma_mem.mp hγ
  have d00 : (M : ℤ) ∣ γ 0 0 - 1 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (γ 0 0) M).mp (by rw [Int.cast_one]; exact h00.symm)
  have d11 : (M : ℤ) ∣ γ 1 1 - 1 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub 1 (γ 1 1) M).mp (by rw [Int.cast_one]; exact h11.symm)
  have d01 : (M : ℤ) ∣ γ 0 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h01
  have d10 : (M : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h10
  obtain ⟨k00, e00⟩ := d00
  obtain ⟨k11, e11⟩ := d11
  obtain ⟨k01, e01⟩ := d01
  obtain ⟨k10, e10⟩ := d10
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have q00 : ((γ 0 0 : ℤ) : ℚ) = 1 + M * k00 := by
    rw [show (γ 0 0 : ℤ) = 1 + M * k00 by linarith]; push_cast; ring
  have q11 : ((γ 1 1 : ℤ) : ℚ) = 1 + M * k11 := by
    rw [show (γ 1 1 : ℤ) = 1 + M * k11 by linarith]; push_cast; ring
  have q01 : ((γ 0 1 : ℤ) : ℚ) = M * k01 := by rw [e01]; push_cast; ring
  have q10 : ((γ 1 0 : ℤ) : ℚ) = M * k10 := by rw [e10]; push_cast; ring
  refine ⟨![a * k00 + b * k10, a * k01 + b * k11], ?_⟩
  funext i
  fin_cases i
  · simp only [act, Fin.sum_univ_two]
    simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    rw [q00, q10, ha, hb]; push_cast; field_simp; ring
  · simp only [act, Fin.sum_univ_two]
    simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.head_cons]
    rw [q01, q11, ha, hb]; push_cast; field_simp; ring

theorem siegel_level : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε) (c : ℕ)
    (x : Fin 2 → ℚ) (M : ℕ), admitted c x → 0 < M → (∃ a b : ℤ, x 0 = a / M ∧ x 1 = b / M) →
    ∀ γ ∈ CongruenceSubgroup.Gamma M, T.sl (ofSL γ) (siegel T c x) = siegel T c x := by
  intro Ω _ _ _ ε T c x M hx hM hden γ hγ
  rw [GlobalTheory.T.siegelUnitInTower_sl_action_rowVector Ω ε T c x γ hx]
  obtain ⟨n, hn⟩ := act_sub_int_of_Gamma x M hM hden γ hγ
  have hs : sgC c (act x γ) = sgC c x := by
    rw [hn]; funext z; exact GlobalTheory.T.smoothedSiegelUnit_index_add_intVector c x n _ hx
  unfold siegel
  rw [hs]

end GlobalTheory.KZ
