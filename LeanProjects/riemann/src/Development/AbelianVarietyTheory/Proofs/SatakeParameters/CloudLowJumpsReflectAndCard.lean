import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem block_map_reflect (R : Ranks) :
    (block R).map (fun u => (R.t : ℤ) - 1 - u) = block R := by
  have hnd : (block R).Nodup := by
    unfold block
    exact (Multiset.nodup_range R.t).map (fun a b h => by exact_mod_cast h)
  have hmem : ∀ x : ℤ, x ∈ block R ↔ 0 ≤ x ∧ x < R.t := by
    intro x
    unfold block
    simp only [Multiset.mem_map, Multiset.mem_range]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨by positivity, by exact_mod_cast hc⟩
    · rintro ⟨h0, h1⟩
      exact ⟨x.toNat, by omega, by omega⟩
  refine (Multiset.Nodup.ext (hnd.map (fun a b h => by simpa using h)) hnd).2 ?_
  · intro x
    rw [Multiset.mem_map, hmem]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hmem] at hy
      omega
    · rintro ⟨h0, h1⟩
      exact ⟨(R.t : ℤ) - 1 - x, by rw [hmem]; omega, by ring⟩

theorem jR_symm_card {R : Ranks} (P : HCParam R) (j : Fin R.m) :
    jR P j false = (jR P j true).map (fun u => (R.t : ℤ) - 1 - u) ∧ ∀ s, (jW P j s).card = R.r ∧
      (jR P j s).card = R.nV ∧ (jT2 P j s).card = R.r ∧ jT2 P j s ≤ jT1 P j s := by
  have hk : 1 ≤ R.k := by have := R.m_add_three_le_k; omega
  have hW : ∀ s, (jW P j s).card = R.r := by
    intro s
    have h : (cloud P j + lows P j).card = R.r := by
      simp only [Multiset.card_add, cloud, lows, Multiset.card_map, Finset.card_val,
        Finset.card_univ, Fintype.card_fin, Ranks.r]
      omega
    cases s
    · simp only [jW, Bool.false_eq_true, if_false, Multiset.card_map, h]
    · simp only [jW, if_true, h]
  refine ⟨?_, fun s => ?_⟩
  · simp only [jR, jW, if_true, Bool.false_eq_true, if_false, Multiset.map_add, block_map_reflect]
  · have hR : (jR P j s).card = R.nV := by
      simp only [jR, Multiset.card_add, hW s, block, Multiset.card_map, Multiset.card_range, Ranks.nV]
    refine ⟨hW s, hR, ?_, ?_⟩
    · simp only [jT2, Multiset.card_map, hW s]
    · unfold jT2 jT1 jR
      exact Multiset.map_le_map (Multiset.le_add_right _ _)

end GlobalTheory.HTW
