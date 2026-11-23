import Formalism.LocalToGlobal.Columns.LevGSym
import Formalism.LocalToGlobal.HermitianForms.DefsSym
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CongruenceLevelEqDepthSucc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhiTopTargetSym
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.JoinForms
import Formalism.LocalToGlobal.Columns.LevGCount
open Formalism.L2.Col

namespace GlobalTheory.MemXSym

open Formalism.L2.Forms

theorem facts {n k r t m rS : ℕ} (hr : r = k + 2 * rS + 1) (ht : 0 < t) (hn : n = r + m * t + 1) (x : ℕ) (hx : x < n) :
    (x < r ∧ coarse r (List.replicate m t) x = 0 ∧ lvSym k rS t x = symIdx k rS x ∧ symIdx k rS x < r) ∨
    (r ≤ x ∧ lvSym k rS t x + 1 = r + coarse r (List.replicate m t) x ∧ 1 ≤ coarse r (List.replicate m t) x) := by
  rcases Nat.lt_or_ge x r with h1 | h1
  · refine Or.inl ⟨h1, coarse_of_lt h1, ?_, ?_⟩
    · have : x < rSym k rS := by unfold rSym; omega
      rw [lvSym_of_lt this]; unfold posSym symIdx; split_ifs <;> omega
    · unfold symIdx; split_ifs <;> omega
  · refine Or.inr ⟨h1, ?_, by rw [coarse_of_le h1]; omega⟩
    have hx' : ¬ x < rSym k rS := by unfold rSym; omega
    have hs : rSym k rS = r := by unfold rSym; omega
    unfold lvSym; rw [if_neg hx', hs]
    rcases Nat.lt_or_ge x (r + m * t) with h2 | h2
    · rw [GlobalTheory.TopLawSym.coarse_eq ht h1 h2, Nat.add_assoc]
    · have hx2 : x = r + m * t := by omega
      subst hx2
      rw [coarse_of_le h1, blkIdx_replicate_of_le t m (r + m * t - r) (by omega), Nat.add_sub_cancel_left,
        Nat.mul_div_cancel _ ht, Nat.add_assoc]

theorem facts_lt {k r t rS x : ℕ} (hr : r = k + 2 * rS + 1) (hx : x < r) :
    lvSym k rS t x = symIdx k rS x := by
  have : x < rSym k rS := by unfold rSym; omega
  rw [lvSym_of_lt this]; unfold posSym symIdx; split_ifs <;> omega

theorem coarse_last {r t m x : ℕ} (hx : x < r + m * t) :
    coarse r (List.replicate m t) x < coarse r (List.replicate m t) (r + m * t) := by
  have cN : coarse r (List.replicate m t) (r + m * t) = m + 1 := by
    rw [coarse_of_le (by omega), blkIdx_replicate_of_le t m (r + m * t - r) (by omega)]
  rw [cN]
  rcases Nat.lt_or_ge x r with h1 | h1
  · rw [coarse_of_lt h1]; omega
  · rw [coarse_of_le h1]; have := blkIdx_replicate_lt t m (x - r) (by omega); omega

variable {κ : Type} [Field κ]

theorem inJ_of_mem {n k r t m rS : ℕ} (h : r ≤ n) (hr : r = k + 2 * rS + 1) (ht : 0 < t) (hn : n = r + m * t + 1)
    {M : GL (Fin n) κ} (hM : M ∈ HXmsym κ n k r t m rS h) : InJSym k rS t true (M : Matrix (Fin n) (Fin n) κ) := by
  obtain ⟨hJ, hF⟩ := Subgroup.mem_inf.mp hM
  have hF' : ∀ i j : Fin n, j.val = r + m * t → (M : Matrix (Fin n) (Fin n) κ) i j = (1 : Matrix (Fin n) (Fin n) κ) i j := hF
  obtain ⟨hB, h0⟩ := mem_HPar.mp hJ
  have hkr : k + rS ≤ r := by omega
  rw [mem_HPsymF_iff hkr] at h0
  obtain ⟨p1, p2, p3⟩ := h0
  refine ⟨fun x y hxy => ?_, fun x hx => ?_, fun x y hx hy => ?_, fun _ x y hy => ?_⟩
  · rcases facts hr ht hn x.val x.2 with ⟨hx, cx, lx, sx⟩ | ⟨hx, lx, cx⟩ <;>
      rcases facts hr ht hn y.val y.2 with ⟨hy, cy, ly, sy⟩ | ⟨hy, ly, cy⟩
    · rw [lx, ly] at hxy
      exact p1 ⟨x, hx⟩ ⟨y, hy⟩ hxy
    · exfalso; omega
    · exact (mem_btG.mp hB) x y (by omega)
    · exact (mem_btG.mp hB) x y (by omega)
  · exact p2 ⟨x, by unfold rSym at hx; omega⟩
  · exact p3 ⟨x, by omega⟩ ⟨y, by omega⟩ hx hy
  · have hy' : y.val = r + m * t := by omega
    constructor
    · rw [hF' x y hy', Matrix.one_apply]
    · by_cases hxy : x = y
      · subst hxy; rw [hF' x x hy', Matrix.one_apply]
      · rw [if_neg hxy]
        apply (mem_btG.mp hB) y x
        have hx1 : x.val < r + m * t := by
          have := x.2; have : x.val ≠ y.val := fun e => hxy (Fin.ext e); omega
        rw [hy']
        exact coarse_last hx1

theorem mem_of_inJ {n k r t m rS : ℕ} (h : r ≤ n) (hr : r = k + 2 * rS + 1) (ht : 0 < t) (hn : n = r + m * t + 1)
    {M : GL (Fin n) κ} (hM : InJSym k rS t true (M : Matrix (Fin n) (Fin n) κ)) : M ∈ HXmsym κ n k r t m rS h := by
  obtain ⟨q1, q2, q3, q4⟩ := hM
  have hkr : k + rS ≤ r := by omega
  have hB : M ∈ blockUT n κ r (List.replicate m t) := mem_btG.mpr fun x y hxy => q1 x y (by
    rcases facts hr ht hn x.val x.2 with ⟨hx, cx, lx, sx⟩ | ⟨hx, lx, cx⟩ <;>
      rcases facts hr ht hn y.val y.2 with ⟨hy, cy, ly, sy⟩ | ⟨hy, ly, cy⟩ <;> omega)
  refine Subgroup.mem_inf.mpr ⟨mem_HPar.mpr ⟨hB, ?_⟩, ?_⟩
  · rw [mem_HPsymF_iff hkr]
    refine ⟨fun i j hij => ?_, fun i => ?_, fun i j hi hj => ?_⟩
    · refine q1 (Fin.castLE h i) (Fin.castLE h j) ?_
      simp only [Fin.coe_castLE]
      rw [facts_lt hr i.2, facts_lt hr j.2]
      exact hij
    · exact q2 (Fin.castLE h i) (by simp only [Fin.coe_castLE]; unfold rSym; omega)
    · exact q3 (Fin.castLE h i) (Fin.castLE h j) (by simpa using hi) (by simpa using hj)
  · intro x y hy
    rw [(q4 rfl x y (by omega)).1, Matrix.one_apply]

theorem memX (κ : Type) [Field κ] (n k r t m rS : ℕ) (h : r ≤ n) (hr : r = k + 2 * rS + 1) (ht : 0 < t)
    (hn : n = r + m * t + 1) (M : GL (Fin n) κ) :
    M ∈ HXmsym κ n k r t m rS h ↔ M ∈ Formalism.L2.Forms.JSymG κ n k rS t true := by
  constructor
  · intro hM
    show InJSym k rS t true _ ∧ InJSym k rS t true _
    exact ⟨inJ_of_mem h hr ht hn hM, inJ_of_mem h hr ht hn (Subgroup.inv_mem _ hM)⟩
  · intro hM
    exact mem_of_inJ h hr ht hn hM.1

end GlobalTheory.MemXSym
