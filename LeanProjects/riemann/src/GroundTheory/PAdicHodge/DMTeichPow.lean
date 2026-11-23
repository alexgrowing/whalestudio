import Mathlib
import GroundTheory.PAdicHodge.ExistsWeightLeOfConvergesAt
import GroundTheory.PAdicHodge.ExtRobbaDMLinear
set_option maxSynthPendingDepth 1

noncomputable section

set_option linter.unusedSectionVars false

namespace GroundTheory.PAdicHodge

namespace TeichLift

open UniformSpace

variable {p : ℕ} [hp : Fact p.Prime] {L : Type*} [NontriviallyNormedField L] [IsUltrametricDist L]
  [CharP L p] [PerfectRing L p] {Γ : Type*} [CommRing Γ] {T : TeichLift p L Γ}

namespace TeichFrob

def id (T : TeichLift p L Γ) : T.TeichFrob where
  φ := RingEquiv.refl Γ
  a := 0
  red_φ x := by simp
  u := 1
  φ_π := by simp
  u_mem_int := one_mem _
  norm_red_u := by simp
  map_int _ hx := hx
  symm_map_int _ hx := hx

def comp (F G : T.TeichFrob) : T.TeichFrob where
  φ := G.φ.trans F.φ
  a := F.a + G.a
  red_φ x := by
    simp only [RingEquiv.trans_apply, F.red_φ, G.red_φ, ← pow_mul, pow_add, mul_comm]
  u := F.u * F.φ G.u
  φ_π := by
    simp only [RingEquiv.trans_apply, G.φ_π, map_mul, F.φ_π]
    ring
  u_mem_int := mul_mem F.u_mem_int (F.map_int _ G.u_mem_int)
  norm_red_u := by
    rw [map_mul, norm_mul, F.norm_red_u, F.red_φ, norm_pow, G.norm_red_u, one_pow, one_mul]
  map_int x hx := F.map_int _ (G.map_int _ hx)
  symm_map_int x hx := G.symm_map_int _ (F.symm_map_int _ hx)

variable (F G : T.TeichFrob)

theorem comp_φ_apply (x : Γ) : (F.comp G).φ x = F.φ (G.φ x) := rfl

theorem comp_a : (F.comp G).a = F.a + G.a := rfl

def pow : ℕ → T.TeichFrob
  | 0 => id T
  | d + 1 => F.comp (pow d)

theorem pow_zero : F.pow 0 = id T := rfl

theorem pow_succ (d : ℕ) : F.pow (d + 1) = F.comp (F.pow d) := rfl

theorem pow_φ_apply (d : ℕ) (x : Γ) : (F.pow d).φ x = F.φ^[d] x := by
  induction d with
  | zero => rfl
  | succ d ih => rw [pow_succ, comp_φ_apply, ih, Function.iterate_succ_apply']

theorem pow_a (d : ℕ) : (F.pow d).a = F.a * d := by
  induction d with
  | zero => rfl
  | succ d ih => rw [pow_succ, comp_a, ih]; ring

theorem pow_a_pos {d : ℕ} (ha : 0 < F.a) (hd : 0 < d) : 0 < (F.pow d).a := by
  rw [pow_a]; exact Nat.mul_pos ha hd

theorem exists_iterate_φ_eq_mul_of_mem_Gcon [IsAlgClosed L] (ha : 0 < F.a) {d : ℕ} (hd : 0 < d)
    {w : Γ} (hw : w ∈ T.Gcon) (hw0 : T.red w ≠ 0) :
    ∃ y ∈ T.Gcon, T.red y ≠ 0 ∧ F.φ^[d] y = w * y := by
  obtain ⟨y, hy, hy0, hyw⟩ := (F.pow d).exists_φ_eq_mul_of_mem_Gcon (F.pow_a_pos ha hd) hw hw0
  exact ⟨y, hy, hy0, by rw [← pow_φ_apply]; exact hyw⟩

end TeichFrob

end TeichLift

end GroundTheory.PAdicHodge
