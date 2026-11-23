import Mathlib
import Formalism.SharpRestriction.ParConsts
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TopRowsParams
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.AlTop

theorem al_le_rowLen_sub {D : D7} (L : SizeData₂ D) (u : D.what₂.Word) (j : ℕ) (hj : j < D.R.m)
    (t : HH D) (ht : t ∈ D.host.TT) :
    al L (aL L) t ≤ (((nuD D u j (false, t)).rowLen 0 : ℕ) : ℝ) - (((nuD D u j (false, t)).rowLen 1 : ℕ) : ℝ) := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hN : D.R.k ≤ D.R.N j := by unfold Ranks.N; omega
  have hz : IsTopPl D (false, t) := ⟨rfl, ht⟩
  obtain ⟨e1, -⟩ := GlobalTheory.TopRows.nuRow_tauPl_of_isTopPl L u j hj (false, t) hz
  have hwe : wPl D (j + 1) (false, t) = (((D.hcW u (tauPl D (false, t))).e ⟨j, hj⟩ : ℚ) : ℝ) := by
    unfold wPl wj
    rw [dif_pos (by simpa using hj), D.hcW_e]
    rfl
  obtain ⟨-, h4⟩ := L.cloud_u u (tauPl D (false, t)) ⟨1, by omega⟩ le_rfl (by show 1 + 1 < D.R.k; omega)
  have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hS := L.Sc_pos
  rw [nuRowOK D u j hj, nuRowOK D u j hj, if_pos (by omega), if_pos (by omega), e1,
    RowWeightLemmas.nuRow_head D u j hj _ 1 (by omega), hwe]
  unfold al cG kaJ Ranks.N
  push_cast
  linarith

theorem al_le : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ t ∈ (Fm.D x i).host.TT, al (Fm.L x i) (aL (Fm.L x i)) t ≤ (((nuD (Fm.D x i) u j (false, t)).rowLen 0 : ℕ) : ℝ) - (((nuD (Fm.D x i) u j (false, t)).rowLen 1 : ℕ) : ℝ) :=
  fun Fm => ⟨0, fun x _ _ i u j hj t ht => al_le_rowLen_sub (Fm.L x i) u j hj t ht⟩

end GlobalTheory.AlTop
