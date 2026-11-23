import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.SizeThick

theorem size_thick {D : D7} (L : SizeData₂ D) (g : D.R.GG) (j : Fin D.R.m) (hT : Thick D.host g) :
    L.sc.b ≤ (⌊(hcAt D g).e j⌋ : ℝ) ∧ (⌊(hcAt D g).e j⌋ : ℝ) ≤ L.sc.b + L.etaSz + 1 := by
  set ρ := D.eTau.symm ⟨plc g, plc_mem g⟩ with hρ
  have hw : wj D (j.1 + 1) ρ = (((D.hc ρ).e j : ℚ) : ℝ) := by
    have hj' : j.1 + 1 - 1 < D.R.m := by have := j.2; omega
    rw [wj, dif_pos hj']
    have : (⟨j.1 + 1 - 1, hj'⟩ : Fin D.R.m) = j := Fin.ext (by simp)
    rw [this]
  have hmem : (D.eTau ρ : D.R.GG) ∈ D.host.thickPlaces := by
    rw [hρ, Equiv.apply_symm_apply]; exact hT
  have h := L.win_thick (j.1 + 1) (by omega) j.2 ρ hmem
  rw [hw] at h
  have hc : hcAt D g = D.hc ρ := rfl
  obtain ⟨z, hz⟩ := (D.hc ρ).e_int j
  rw [hc, hz, Int.floor_intCast]
  rw [hz] at h
  push_cast at h ⊢
  exact h

end GlobalTheory.HTW.SizeThick
