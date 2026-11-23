import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem size_not_thick : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (g : D.R.GG) (j : Fin D.R.m), Roomy L C → ¬ Thick D.host g → L.sc.w'' D.R.n ≤ (⌊(hcAt D g).e j⌋ : ℝ) ∧ (⌊(hcAt D g).e j⌋ : ℝ) ≤ 8 / 5 * L.sc.b' := by
  intro D L C g j hR hnt
  obtain ⟨-, hw100, hwη, hwb, hbT, -⟩ := hR
  set ρ := D.eTau.symm ⟨plc g, plc_mem g⟩ with hρ
  have hρe : (D.eTau ρ : D.R.GG) = plc g := by rw [hρ, Equiv.apply_symm_apply]
  have hj : j.1 + 1 ≤ D.R.m := j.2
  have hw : wj D (j.1 + 1) ρ = (((D.hc ρ).e j : ℚ) : ℝ) := by
    have hj' : j.1 + 1 - 1 < D.R.m := by have := j.2; omega
    rw [wj, dif_pos hj']
    have : (⟨j.1 + 1 - 1, hj'⟩ : Fin D.R.m) = j := Fin.ext (by simp)
    rw [this]
  obtain ⟨z, hz⟩ := (D.hc ρ).e_int j
  have hfl : (⌊(hcAt D g).e j⌋ : ℝ) = wj D (j.1 + 1) ρ := by
    rw [hw]
    show (⌊(D.hc ρ).e j⌋ : ℝ) = (((D.hc ρ).e j : ℚ) : ℝ)
    rw [hz, Int.floor_intCast]; push_cast; rfl
  rw [hfl]
  have hx : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hb' : 0 < L.sc.b' := by linarith
  have hq : 0 < L.sc.b' / L.sc.x := div_pos hb' hx
  have hS := L.Sc_pos
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hnt' : (D.eTau ρ : D.R.GG) ∉ D.host.thickPlaces := by rw [hρe]; exact hnt
  by_cases h2 : (D.eTau ρ : D.R.GG) ∈ D.host.topPlaces
  · obtain ⟨t, ht', e⟩ := Finset.mem_image.mp h2
    obtain ⟨a1, a2⟩ := L.win_top _ (by omega) hj ρ ⟨t, ht'⟩ e.symm
    have a3 := L.bT_ge ⟨t, ht'⟩
    have a4 := hbT ⟨t, ht'⟩
    constructor <;> linarith
  · obtain ⟨a1, a2⟩ := L.win_thin _ (by omega) hj ρ ⟨(D.eTau ρ).2, h2, hnt'⟩
    constructor <;> linarith

end GlobalTheory.HTW
