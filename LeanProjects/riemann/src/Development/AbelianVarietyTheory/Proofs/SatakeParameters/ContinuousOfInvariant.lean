import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.FourierColumnIndicator

open MeasureTheory

noncomputable section

namespace GlobalTheory.PadicFourierLattice

open GlobalTheory.IndefiniteRowSideFullHecke.FourierColumnIndicator

variable {g : ℕ} [hg : Fact g.Prime] {n : ℕ}

lemma g_ne : (g : ℚ_[g]) ≠ 0 := by exact_mod_cast hg.out.ne_zero

lemma gR_pos : (0 : ℝ) < g := by exact_mod_cast hg.out.pos

lemma norm_g : ‖(g : ℚ_[g])‖ = (g : ℝ)⁻¹ := Padic.norm_p

lemma norm_le_inv {x : ℚ_[g]} (h : ‖x‖ < 1) : ‖x‖ ≤ (g : ℝ)⁻¹ := by
  have := (Padic.norm_le_pow_iff_norm_lt_pow_add_one x (-1)).2 (by simpa using h)
  simpa using this

lemma norm_div_g_le {x : ℚ_[g]} (h : ‖x‖ < 1) : ‖x / (g : ℚ_[g])‖ ≤ 1 := by
  rw [norm_div, norm_g, div_le_one (inv_pos.2 gR_pos)]
  exact norm_le_inv h

lemma exists_rep (x : ℚ_[g]) (h : ‖(g : ℚ_[g]) * x‖ ≤ 1) :
    ∃ t : Fin g, ‖x - ((t : ℕ) : ℚ_[g]) / (g : ℚ_[g])‖ ≤ 1 := by
  let z : ℤ_[g] := ⟨(g : ℚ_[g]) * x, h⟩
  refine ⟨⟨PadicInt.zmodRepr z, PadicInt.zmodRepr_lt_p z⟩, ?_⟩
  have h1 := PadicInt.sub_zmodRepr_mem z
  rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits] at h1
  have h2 : ‖(g : ℚ_[g]) * x - ((PadicInt.zmodRepr z : ℕ) : ℚ_[g])‖ < 1 := by
    rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at h1
    exact h1
  have h3 := norm_div_g_le h2
  rwa [sub_div, mul_div_cancel_left₀ _ g_ne] at h3

end GlobalTheory.PadicFourierLattice
