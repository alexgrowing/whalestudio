import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTriSelf
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.Vert GlobalTheory.TriFrame GlobalTheory.FlagCell
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO SCF)

namespace GlobalTheory.TriFrame

theorem matNorm_pos_of_isUnit (C : Type) [NontriviallyNormedField C] (r : ℕ) (M : Matrix (Fin r) (Fin r) C)
    (hM : IsUnit M) (i : Fin r) : 0 < matNorm M i := by
  obtain ⟨N, hN⟩ := hM.exists_left_inv
  have hS : 0 ≤ ∑ l, ‖N i l‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hT : 0 ≤ ∑ l, ‖M l i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hb : 0 < (∑ l, ‖N i l‖ + 1)⁻¹ := by positivity
  refine hb.trans_le (le_csInf ?_ ?_)
  · obtain ⟨c, hc0, hc⟩ := NormedField.exists_norm_lt C (r := (∑ l, ‖M l i‖ + 1)⁻¹) (by positivity)
    refine ⟨_, Pi.single i c, by simpa using hc0, fun k hk => by simp [hk.ne'], fun l => ?_, rfl⟩
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same, norm_mul]
    have h1 : ‖M l i‖ ≤ ∑ l, ‖M l i‖ :=
      Finset.single_le_sum (f := fun l => ‖M l i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ l)
    calc ‖c‖ * ‖M l i‖ ≤ (∑ l, ‖M l i‖ + 1)⁻¹ * (∑ l, ‖M l i‖ + 1) := by
          gcongr
          linarith
      _ = 1 := inv_mul_cancel₀ (by positivity)
  · rintro _ ⟨cf, h₁, -, h₂, rfl⟩
    have hcf : cf i = ∑ l, N i l * ∑ j, cf j * M l j := by
      have : cf = N.mulVec (M.mulVec cf) := by rw [Matrix.mulVec_mulVec, hN, Matrix.one_mulVec]
      conv_lhs => rw [this]
      simp only [Matrix.mulVec, dotProduct, mul_comm]
    refine inv_anti₀ (norm_pos_iff.2 h₁) ?_
    rw [hcf]
    refine (norm_sum_le _ _).trans (le_trans (Finset.sum_le_sum fun l _ => ?_) (le_add_of_nonneg_right zero_le_one))
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (h₂ l)

end GlobalTheory.TriFrame
