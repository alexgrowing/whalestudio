import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc
import Formalism.LocalToGlobal.GaloisLevelStructure.TiedLevel
import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.SelfDualFramesExistOfDiagonal
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.WtPar

lemma univ_map_eq_range {α : Type} (n : ℕ) (f : ℕ → α) :
    (Finset.univ : Finset (Fin n)).val.map (fun i : Fin n => f (i : ℕ)) = (Multiset.range n).map f := by
  rw [Fin.univ_val_map, List.ofFn_eq_map, Multiset.range, Multiset.map_coe, ← List.map_coe_finRange_eq_range,
    List.map_map]
  rfl

lemma transport {D : D7} {j : ℕ} {τ : D.what₂.Tau} {n n' : ℕ} (h : n = n')
    (hx : ∃ lam : DomWeight n, Bridge.IsLamPrime (D := D) lam j τ) :
    ∃ lam : DomWeight n', Bridge.IsLamPrime (D := D) lam j τ := by
  subst h; exact hx

lemma lamPrime_add_rho (W : Formalism.IndefR.IndefiniteWeightData.WeightData) (hk : 1 ≤ W.k) (hj : 1 ≤ W.j) (hjm : W.j ≤ W.m)
    (i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ W.nV) :
    W.lamPrime i + W.rhoNV i = W.uSideTarget i - 1 / 2 := by
  have hN : W.nV = W.p + W.q + W.t := by
    simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.nV, Formalism.IndefR.IndefiniteWeightData.WeightData.r,
      Formalism.IndefR.IndefiniteWeightData.WeightData.p, Formalism.IndefR.IndefiniteWeightData.WeightData.q]; omega
  have hNq : (W.nV : ℚ) = W.p + W.q + W.t := by exact_mod_cast hN
  simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.lamPrime, Formalism.IndefR.IndefiniteWeightData.WeightData.thetaWt,
    Formalism.IndefR.IndefiniteWeightData.WeightData.dTau, Formalism.IndefR.IndefiniteWeightData.WeightData.rhoNV,
    Formalism.IndefR.IndefiniteWeightData.WeightData.uSideTarget, Formalism.IndefR.IndefiniteWeightData.WeightData.aPlus,
    Formalism.IndefR.IndefiniteWeightData.WeightData.aMinus]
  split_ifs with h1 h2
  · ring
  · rw [hNq]; ring
  · have hc : W.q + 1 - (W.q + 1 - (i - W.p - W.t)) = i - W.p - W.t := by omega
    rw [hc]
    have hc' : ((i - W.p - W.t : ℕ) : ℚ) = i - W.p - W.t := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    rw [hc', hNq]; ring

end GlobalTheory.Mem.WtPar

namespace GlobalTheory.Mem.WtPar

theorem infOf_lamLdef_eq_paramV : ∀ (D : D7) (j : Fin D.R.m) (τ : D.what₂.Tau),
    NG.infOf (Bridge.lamLdef (D := D) D.R.nV ((j : ℕ) + 1) τ).w = NG.paramV D.R (D.hc τ) j (1 / 2) := by
  intro D j τ
  have hk := D.R.m_add_three_le_k
  have hjm := j.2
  have hex : ∃ lam : DomWeight D.R.nV, Bridge.IsLamPrime (D := D) lam ((j : ℕ) + 1) τ := by
    have h0 := GlobalTheory.ForcedWeights.lamLForced D ((j : ℕ) + 1) (by omega) (by omega) τ
    have hr : (D.sp.V ((j : ℕ) + 1)).rank = D.R.nV := D.sp.V_rank _ (by omega) (by omega)
    exact transport hr ⟨_, h0⟩
  have hl : Bridge.IsLamPrime (D := D) (Bridge.lamLdef (D := D) D.R.nV ((j : ℕ) + 1) τ) ((j : ℕ) + 1) τ := by
    unfold Bridge.lamLdef; rw [dif_pos hex]; exact hex.choose_spec
  set lam := Bridge.lamLdef (D := D) D.R.nV ((j : ℕ) + 1) τ
  obtain ⟨hj, W, hWk, hWm, hWt, hWj, hWe, hWv, hWb, hw⟩ := hl
  have hWn : W.nV = D.R.nV := by
    simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.nV, Formalism.IndefR.IndefiniteWeightData.WeightData.r, Ranks.nV, Ranks.r, hWk, hWm, hWt]
  have hWp : W.p = D.R.k + (j : ℕ) := by
    simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.p, hWk, hWj]; omega
  let g : ℕ → ℚ := fun i => W.uSideTarget (i + 1) - 1 / 2

  have hL : NG.infOf lam.w = (Multiset.range D.R.nV).map (fun i => ((g i : ℚ) : ℂ)) := by
    unfold NG.infOf
    rw [← univ_map_eq_range]
    refine Multiset.map_congr rfl fun i _ => ?_
    have h1 := lamPrime_add_rho W (by omega) (by omega) (by omega) ((i : ℕ) + 1) (by omega)
      (by have := i.2; omega)
    have h2 := hw i
    have key : ((lam.w i : ℤ) : ℚ) + ((D.R.nV : ℚ) - 1) / 2 - ((i : ℕ) : ℚ) = g i := by
      simp only [g]
      rw [h2, ← h1]
      simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.rhoNV, hWn]
      push_cast; ring
    have := congrArg (fun x : ℚ => (x : ℂ)) key
    push_cast at this ⊢
    exact this

  let gv : ℕ → ℚ := fun n => (W.v (n + 2) : ℚ) - 1 / 2
  let gb : ℕ → ℚ := fun n => -(W.b (n + 1) : ℚ) - 1 / 2
  let ge : ℕ → ℚ := fun c => -(W.e : ℚ) - 1 / 2 + ((D.R.t : ℚ) - 1 - 2 * c) / 2
  have hR : NG.paramV D.R (D.hc τ) j (1 / 2) =
      ((Multiset.range (D.R.k - 1)).map gv + (Multiset.range D.R.m).map gb
        + (Multiset.range D.R.t).map ge).map (fun x : ℚ => (x : ℂ)) := by
    simp only [Multiset.map_add, Multiset.map_map]
    unfold NG.paramV
    congr 1
    · congr 1
      · rw [← univ_map_eq_range]
        refine Multiset.map_congr rfl fun i _ => ?_
        simp only [Function.comp, gv, hWv i]
        push_cast; ring
      · rw [← univ_map_eq_range]
        refine Multiset.map_congr rfl fun i _ => ?_
        simp only [Function.comp, gb, hWb i]
        push_cast; ring
    · refine Multiset.map_congr rfl fun c _ => ?_
      have he : (D.hc τ).e j = (W.e : ℚ) := by
        rw [hWe]; congr 1; try (ext; simp)
      simp only [Function.comp, ge, he]
      push_cast; ring
  rw [hL, hR, show (fun i => ((g i : ℚ) : ℂ)) = (fun x : ℚ => (x : ℂ)) ∘ g from rfl, ← Multiset.map_map]
  congr 1

  have hsplit : D.R.nV = ((D.R.k - 1) + ((j : ℕ) + 1)) + D.R.t + (D.R.m - ((j : ℕ) + 1)) := by
    simp only [Ranks.nV, Ranks.r]; omega
  have hmsplit : D.R.m = ((j : ℕ) + 1) + (D.R.m - ((j : ℕ) + 1)) := by omega
  rw [hsplit, Multiset.range_add, Multiset.range_add, Multiset.range_add]
  conv_rhs => rw [hmsplit, Multiset.range_add]
  simp only [Multiset.map_add, Multiset.map_map]
  have e1 : (Multiset.range (D.R.k - 1)).map g = (Multiset.range (D.R.k - 1)).map gv := by
    refine Multiset.map_congr rfl fun n hn => ?_
    rw [Multiset.mem_range] at hn
    simp only [g, gv, Formalism.IndefR.IndefiniteWeightData.WeightData.uSideTarget, Formalism.IndefR.IndefiniteWeightData.WeightData.lam, hWp, hWk]
    rw [if_pos (by omega), if_pos (by omega)]
  have e2 : (Multiset.range ((j : ℕ) + 1)).map (g ∘ fun x => D.R.k - 1 + x) =
      (Multiset.range ((j : ℕ) + 1)).map gb := by
    refine Multiset.map_congr rfl fun n hn => ?_
    rw [Multiset.mem_range] at hn
    simp only [Function.comp, g, gb, Formalism.IndefR.IndefiniteWeightData.WeightData.uSideTarget, Formalism.IndefR.IndefiniteWeightData.WeightData.lam,
      hWp, hWk]
    rw [if_pos (by omega), if_neg (by omega)]
    have hh : D.R.k - 1 + n + 1 - (D.R.k - 1) = n + 1 := by omega
    rw [hh]; push_cast; ring
  have e3 : (Multiset.range D.R.t).map (g ∘ fun x => D.R.k - 1 + ((j : ℕ) + 1) + x) =
      (Multiset.range D.R.t).map ge := by
    refine Multiset.map_congr rfl fun c hc => ?_
    rw [Multiset.mem_range] at hc
    simp only [Function.comp, g, ge, Formalism.IndefR.IndefiniteWeightData.WeightData.uSideTarget, hWp, hWt]
    rw [if_neg (by omega), if_pos (by omega)]
    have : ((D.R.k - 1 + ((j : ℕ) + 1) + c + 1 : ℕ) : ℚ) - ((D.R.k + (j : ℕ) : ℕ) : ℚ) = c + 1 := by
      rw [show D.R.k - 1 + ((j : ℕ) + 1) + c + 1 = (D.R.k + (j : ℕ)) + (c + 1) by omega]
      push_cast; ring
    rw [this]; ring
  have e4 : (Multiset.range (D.R.m - ((j : ℕ) + 1))).map (g ∘ fun x => D.R.k - 1 + ((j : ℕ) + 1) + D.R.t + x) =
      (Multiset.range (D.R.m - ((j : ℕ) + 1))).map (gb ∘ fun x => (j : ℕ) + 1 + x) := by
    refine Multiset.map_congr rfl fun c hc => ?_
    rw [Multiset.mem_range] at hc
    simp only [Function.comp, g, gb, Formalism.IndefR.IndefiniteWeightData.WeightData.uSideTarget, hWp, hWt, hWj]
    rw [if_neg (by omega), if_neg (by omega)]
    have hh : (j : ℕ) + 1 + (D.R.k - 1 + ((j : ℕ) + 1) + D.R.t + c + 1 - (D.R.k + (j : ℕ)) - D.R.t) = (j : ℕ) + 1 + c + 1 := by omega
    rw [hh]
  rw [e1, e2, e3, e4]
  abel

end GlobalTheory.Mem.WtPar
