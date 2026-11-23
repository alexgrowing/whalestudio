import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemDivSuppOfDivCycleNeZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CurvePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsMonomialNotMem
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsSegreDivisor
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w

section

variable {K : Type u} [Fintype K] {ι : K → Type v} [∀ k, Fintype (ι k)] {F : Type w} [Field F]

theorem exists_isChart_of_isProjVarF {V : Ideal (MRingOver F ι)} {n : ℕ} (hV : IsProjVarF V n) :
    ∃ i, IsChart V i :=
  ⟨fun k => (hV.1.2.2 k).choose, fun k => (hV.1.2.2 k).choose_spec⟩

theorem ratDiv_one_eq_mapRange (V : Ideal (MRingOver F ι)) (f : MRingOver F ι) :
    ratDiv V f 1 = Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (divCycle V f) := by
  simp [ratDiv, divCycle_one]

theorem cycEval_ratDiv_one_nonneg (J : Ideal (MRingOver F ι) → ℤ) (V : Ideal (MRingOver F ι))
    (f : MRingOver F ι) (h : ∀ W ∈ divSupp V f, 0 ≤ J W) : 0 ≤ cycEval J (ratDiv V f 1) := by
  rw [ratDiv_one_eq_mapRange, cycEval, Finsupp.sum_mapRange_index (by simp), Finsupp.sum]
  exact Finset.sum_nonneg fun W hW => mul_nonneg (Nat.cast_nonneg _)
    (h W (mem_divSupp_of_divCycle_ne_zero (Finsupp.mem_support_iff.mp hW)))

theorem cycEval_ratDiv_one_pos (J : Ideal (MRingOver F ι) → ℤ) (V : Ideal (MRingOver F ι))
    (f : MRingOver F ι) (hne : divCycle V f ≠ 0) (h : ∀ W ∈ divSupp V f, 0 < J W) :
    0 < cycEval J (ratDiv V f 1) := by
  rw [ratDiv_one_eq_mapRange, cycEval, Finsupp.sum_mapRange_index (by simp), Finsupp.sum]
  refine Finset.sum_pos (fun W hW => mul_pos ?_ ?_) (Finsupp.support_nonempty_iff.mpr hne)
  · exact_mod_cast Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hW)
  · exact h W (mem_divSupp_of_divCycle_ne_zero (Finsupp.mem_support_iff.mp hW))

theorem ptDeg_pos {V : Ideal (MRingOver F ι)} (hV : IsProjVarF V 0) {i : ∀ k, ι k}
    (hi : IsChart V i) : 0 < ptDeg V i := by
  have := chart_finite hV hi
  have : Nontrivial (MRingOver F ι ⧸ chartIdeal V i) := ⟨(chart_isField hV hi).exists_pair_ne⟩
  exact Module.finrank_pos

theorem nonneg_of_isFieldIntersection {I : IFamily F ι} (hI : IsFieldIntersection I) :
    ∀ (n : ℕ) (V : Ideal (MRingOver F ι)), IsProjVarF V n →
      ∀ L : Fin n → K → ℤ, (∀ j k, 0 ≤ L j k) → 0 ≤ I V n L := by
  intro n
  induction n with
  | zero =>
    intro V hV L _
    obtain ⟨i, hi⟩ := exists_isChart_of_isProjVarF hV
    rw [hI.1 V L i hV hi]
    exact Nat.cast_nonneg _
  | succ n ih =>
    intro V hV L hL
    obtain ⟨i, hi⟩ := exists_isChart_of_isProjVarF hV
    have hf := isMultiHomog_coordProd (F := F) i (fun k => (L (Fin.last n) k).toNat)
    have hfV := coordProd_not_mem hV.1.1 i hi (fun k => (L (Fin.last n) k).toNat)
    have hsec : IsRatSection V (L (Fin.last n))
        (∏ k, (X ⟨k, i k⟩ : MRingOver F ι) ^ (L (Fin.last n) k).toNat) 1 :=
      ⟨_, 0, hf, isMultiHomog_one, hfV,
        fun h => hV.1.1.ne_top ((Ideal.eq_top_iff_one V).mpr h),
        fun k => by simp [Int.toNat_of_nonneg (hL _ k)]⟩
    rw [← Fin.snoc_init_self (α := fun _ => K → ℤ) L, hI.2 V n (Fin.init L) _ _ 1 hV hsec]
    exact cycEval_ratDiv_one_nonneg _ _ _ fun W hW =>
      ih W (isProjVarF_of_mem_divSupp hV hf hfV hW) _ fun j k => hL _ k

omit [Fintype K] in

theorem const_one_eq_snoc (n : ℕ) :
    (fun _ _ => (1 : ℤ) : Fin (n + 1) → K → ℤ) =
      Fin.snoc (α := fun _ => K → ℤ) (fun _ _ => 1) (fun _ => 1) := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j <;> simp

theorem segre_pos_of_isFieldIntersection (hS : SegreDivisor.Statement.{u, v, w})
    {I : IFamily F ι} (hI : IsFieldIntersection I) :
    ∀ (n : ℕ) (V : Ideal (MRingOver F ι)), IsProjVarF V n → 0 < I V n (fun _ _ => 1) := by
  intro n
  induction n with
  | zero =>
    intro V hV
    obtain ⟨i, hi⟩ := exists_isChart_of_isProjVarF hV
    rw [hI.1 V _ i hV hi]
    exact_mod_cast ptDeg_pos hV hi
  | succ n ih =>
    intro V hV
    obtain ⟨f, hf, hfV, hne⟩ := hS K ι F V n hV
    have hsec : IsRatSection V (fun _ => 1) f 1 :=
      ⟨_, 0, hf, isMultiHomog_one, hfV,
        fun h => hV.1.1.ne_top ((Ideal.eq_top_iff_one V).mpr h), fun k => by simp⟩
    rw [const_one_eq_snoc, hI.2 V n _ _ f 1 hV hsec]
    exact cycEval_ratDiv_one_pos _ _ _ hne fun W hW =>
      ih W (isProjVarF_of_mem_divSupp hV hf hfV hW)

end

theorem Positivity.of_found (hS : SegreDivisor.Statement.{u, v, w}) {K : Type u} [Fintype K]
    (F : Type w) [Field F] (ι : K → Type v) [∀ k, Fintype (ι k)] :
    ReciprocityTheory.ChartRestriction.G.AI.I1.PositivityStatement F ι :=
  fun _ hI V n hV =>
    ⟨fun L hL => nonneg_of_isFieldIntersection hI n V hV L hL,
      segre_pos_of_isFieldIntersection hS hI n V hV⟩

end GroundTheory.Heights₂.Heights.Targets
