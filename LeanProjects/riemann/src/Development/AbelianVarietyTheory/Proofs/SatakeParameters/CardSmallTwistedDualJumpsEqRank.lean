import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries

noncomputable section

namespace GlobalTheory.HTW

open Formalism.BasicNotions Formalism.FrobeniusOrbits

section Count

variable {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool)

def twistedJump (y : ℤ) : ℤ :=
  if s then -(⌊P.e j⌋ + y + ((R.t : ℤ) + 1) / 2) else ⌊P.e j⌋ + y - ((R.t : ℤ) + 1) / 2

theorem twistedDualJumps_eq_hodgeTateJump_images : jT2 P j s =
    (Finset.univ : Finset (Fin (R.k - 1))).val.map (fun i => twistedJump P j s ⌊P.v i⌋) +
      (Finset.univ : Finset (Fin R.m)).val.map (fun i => twistedJump P j s (-⌊P.b i⌋)) := by
  obtain ⟨q, hq⟩ := R.t_odd
  cases s <;>
    simp only [jT2, jW, cloud, lows, twistedJump, Multiset.map_add, Multiset.map_map,
      Function.comp_def, ↓reduceIte, Bool.false_eq_true] <;>
    congr 1 <;>
    refine Multiset.map_congr rfl fun i _ => ?_ <;>
    omega

theorem twistedJump_low_small (η : ℝ) (h : ∀ i, |((P.b i - P.e j : ℚ) : ℝ)| ≤ η) (i : Fin R.m) :
    |twistedJump P j s (-⌊P.b i⌋)| ≤ ((⌊η⌋₊ + R.t + 2 : ℕ) : ℤ) := by
  obtain ⟨zb, hzb⟩ := P.b_int i
  obtain ⟨ze, hze⟩ := P.e_int j
  obtain ⟨q, hq⟩ := R.t_odd
  have hb : ⌊P.b i⌋ = zb := by rw [hzb]; exact Int.floor_intCast zb
  have he : ⌊P.e j⌋ = ze := by rw [hze]; exact Int.floor_intCast ze
  have hr : (((zb - ze : ℤ) : ℝ)) = (((P.b i - P.e j : ℚ) : ℝ)) := by
    rw [hzb, hze]; push_cast; ring
  have hn : (zb - ze).natAbs ≤ ⌊η⌋₊ := by
    apply Nat.le_floor
    rw [Nat.cast_natAbs, Int.cast_abs, hr]
    exact h i
  have habs : |zb - ze| ≤ (⌊η⌋₊ : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hn
  rw [abs_le] at habs ⊢
  unfold twistedJump
  rw [hb, he]
  cases s <;> simp only [↓reduceIte, Bool.false_eq_true] <;> push_cast <;> constructor <;> omega

theorem twistedJump_cloud_large (n : ℕ) (hv : ∀ i, 0 ≤ P.v i) (h : (n : ℤ) < szT P j s)
    (i : Fin (R.k - 1)) : ¬ |twistedJump P j s ⌊P.v i⌋| ≤ (n : ℤ) := by
  obtain ⟨q, hq⟩ := R.t_odd
  have hV : 0 ≤ ⌊P.v i⌋ := Int.floor_nonneg.mpr (hv i)
  unfold twistedJump
  unfold szT at h
  rw [abs_le]
  cases s <;> simp only [↓reduceIte, Bool.false_eq_true] at h ⊢ <;> omega

end Count

theorem card_small_twistedDualJumps_eq_rank {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool) (η : ℝ)
    (hv : ∀ i, 0 ≤ P.v i) (hb : ∀ i, |((P.b i - P.e j : ℚ) : ℝ)| ≤ η)
    (hs : ((⌊η⌋₊ + R.t + 2 : ℕ) : ℤ) < szT P j s) :
    ((jT2 P j s).filter fun u : ℤ => |u| ≤ ((⌊η⌋₊ + R.t + 2 : ℕ) : ℤ)).card = R.m := by
  rw [twistedDualJumps_eq_hodgeTateJump_images, Multiset.filter_add, Multiset.card_add]
  have hc : ((Finset.univ : Finset (Fin (R.k - 1))).val.map
      (fun i => twistedJump P j s ⌊P.v i⌋)).filter
        (fun u : ℤ => |u| ≤ ((⌊η⌋₊ + R.t + 2 : ℕ) : ℤ)) = 0 := by
    rw [Multiset.filter_eq_nil]
    intro u hu
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hu
    exact twistedJump_cloud_large P j s _ hv hs i
  have hl : ((Finset.univ : Finset (Fin R.m)).val.map
      (fun i => twistedJump P j s (-⌊P.b i⌋))).filter
        (fun u : ℤ => |u| ≤ ((⌊η⌋₊ + R.t + 2 : ℕ) : ℤ)) =
      (Finset.univ : Finset (Fin R.m)).val.map (fun i => twistedJump P j s (-⌊P.b i⌋)) := by
    rw [Multiset.filter_eq_self]
    intro u hu
    obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hu
    exact twistedJump_low_small P j s η hb i
  rw [hc, hl]
  simp

end GlobalTheory.HTW
