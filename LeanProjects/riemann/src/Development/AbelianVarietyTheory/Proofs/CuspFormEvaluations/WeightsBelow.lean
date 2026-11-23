import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.RunWeights

theorem size_le_mul {D : D7} {j : ℕ} (x z : WeightFamilies.Wt D j) (c : ℕ) (hc : 1 ≤ c)
    (h1 : ∀ τ i, x.aP τ i ≤ c * z.aP τ i) (h2 : ∀ τ i, x.aM τ i ≤ c * z.aM τ i) (h3 : x.n ≤ c * z.n) :
    x.size ≤ (c : ℝ) * z.size := by
  have hK : (0 : ℝ) ≤ (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) := by positivity
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hS : (∑ τ, ((∑ i, (x.aP τ i : ℝ)) + ∑ i, (x.aM τ i : ℝ))) ≤
      (c : ℝ) * ∑ τ, ((∑ i, (z.aP τ i : ℝ)) + ∑ i, (z.aM τ i : ℝ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun τ _ => ?_
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    refine add_le_add (Finset.sum_le_sum fun i _ => ?_) (Finset.sum_le_sum fun i _ => ?_)
    · exact_mod_cast h1 τ i
    · exact_mod_cast h2 τ i
  have hn : (x.n : ℝ) ≤ (c : ℝ) * z.n := by exact_mod_cast h3
  have hKn := mul_le_mul_of_nonneg_left hn hK
  unfold WeightFamilies.Wt.size
  nlinarith

theorem DF_le {D : D7} {j : ℕ} (x z : WeightFamilies.Wt D j)
    (h1 : ∀ τ i, x.aP τ i ≤ z.aP τ i) (h2 : ∀ τ i, x.aM τ i ≤ z.aM τ i) : WeightAlgebra.DF x ≤ WeightAlgebra.DF z := by
  unfold WeightAlgebra.DF WeightAlgebra.degP
  exact Finset.sum_le_sum fun τ _ =>
    add_le_add (Finset.sum_le_sum fun i _ => h1 τ i) (Finset.sum_le_sum fun i _ => h2 τ i)

theorem weights_below : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ), 1 ≤ j → FamilyHypotheses.HypPage large₂ X H C2 A2 CR CT ka wL wF Tn nP nW h0 → (∀ w ∈ ({wL, wF, X.wF0 wL wF, ka} : Set (WeightFamilies.Wt D j)), WeightAlgebra.DF w ≤ WeightAlgebra.DF ka ∧ w.n ≤ ka.n ∧ D.R.r ≤ w.n ∧ w.LastPos) ∧ (∀ w ∈ ({wF, X.wF0 wL wF, ka} : Set (WeightFamilies.Wt D j)), 8 * D.R.f * D.R.r + 4 ≤ w.n) ∧ (∀ w2, IsG2 wL wF w2 → WeightAlgebra.DF w2 ≤ WeightAlgebra.DF ka ∧ w2.n ≤ ka.n ∧ w2.size ≤ ((WeightFamilies.dimY D j : ℝ) + 4) * wL.size) ∧ (∀ w1, IsDoubledWeightWithShift wL w1 nW → WeightAlgebra.DF w1 ≤ WeightAlgebra.DF ka ∧ w1.n ≤ ka.n ∧ w1.size ≤ 2 * wL.size) := by
  intro D B P j X large₂ H C2 A2 CR CT ka wL wF Tn nP nW h0 hj hH
  unfold FamilyHypotheses.HypPage at hH
  obtain ⟨_, hSet, _, _, _⟩ := hH
  unfold SetC at hSet
  obtain ⟨hkan, _, _, hh0, _, hlastP, _, _, _, hnP8, hnPW, _, _, hnV, hL, hF, _, hT0, hDT, h40, hDnW,
    h40n, _, _, _, hDom⟩ := hSet
  obtain ⟨hLn, hLP, _⟩ := hL
  obtain ⟨hFn, hFP, hFM⟩ := hF

  have kaP : ∀ τ i, ka.aP τ i = Tn * wL.aP τ i + wF.aP τ i := fun τ i => by
    have e := hFP τ i
    have e' : ((ka.aP τ i : ℕ) : ℤ) = ((Tn * wL.aP τ i + wF.aP τ i : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast e'
  have kaM : ∀ τ i, ka.aM τ i = Tn * wL.aM τ i + wF.aM τ i := fun τ i => by
    have e := hFM τ i
    have e' : ((ka.aM τ i : ℕ) : ℤ) = ((Tn * wL.aM τ i + wF.aM τ i : ℕ) : ℤ) := by push_cast; linarith
    exact_mod_cast e'
  have kan : ka.n = nP + Tn * nW := by rw [hkan, hnV]
  have f0P : ∀ τ i, (X.wF0 wL wF).aP τ i = wF.aP τ i + WeightFamilies.dimY D j * wL.aP τ i := fun _ _ => rfl
  have f0M : ∀ τ i, (X.wF0 wL wF).aM τ i = wF.aM τ i + WeightFamilies.dimY D j * wL.aM τ i := fun _ _ => rfl
  have f0n : (X.wF0 wL wF).n = wF.n + WeightFamilies.dimY D j * wL.n := rfl
  have hT1 : 1 ≤ Tn := hT0
  have hT2 : 2 ≤ Tn := by omega
  have hD4 : WeightFamilies.dimY D j + 4 ≤ Tn := by omega

  have hf : 0 < D.R.f := by
    obtain ⟨hC, hCZ, _⟩ := hDom
    have hZ : (0 : ℝ) < Zb D large₂ := lt_of_lt_of_le (by positivity) hCZ
    unfold Zb at hZ
    rcases Nat.eq_zero_or_pos D.R.f with h | h
    · simp [h] at hZ
    · exact h
  have hrP : D.R.r ≤ nP := by
    have e : 8 * D.R.f * D.R.r = 8 * (D.R.f * D.R.r) := by ring
    have := Nat.mul_le_mul hf (le_refl D.R.r)
    omega

  have leKa : ∀ w : WeightFamilies.Wt D j, (∀ τ i, w.aP τ i ≤ ka.aP τ i) → (∀ τ i, w.aM τ i ≤ ka.aM τ i) →
      WeightAlgebra.DF w ≤ WeightAlgebra.DF ka := fun w a b => DF_le w ka a b

  have kaLast : ∀ τ (i : Fin (D.R.sigW j).1), i.1 + 1 = (D.R.sigW j).1 → 2 * Tn * Tn ≤ ka.aP τ i := by
    intro τ i hi
    have e := hlastP τ i hi
    have e' : (2 * (Tn : ℝ) * Tn) ≤ ka.aP τ i := by nlinarith
    exact_mod_cast e'

  have wLLast : ∀ τ (i : Fin (D.R.sigW j).1), i.1 + 1 = (D.R.sigW j).1 →
      1 ≤ wL.aP τ i ∧ ((Tn + WeightFamilies.dimY D j + 2 : ℕ) : ℤ) * wL.aP τ i ≤
        (ka.aP τ i : ℤ) - ((WeightFamilies.dimY D j : ℤ) + 2) * nW - 2 * D.R.r := by
    intro τ i hi
    have e := hLP τ i
    unfold gapZ at e
    rw [dif_neg (by omega), if_neg (by omega)] at e
    unfold Tp at e
    have hb : (0 : ℤ) < ((Tn + WeightFamilies.dimY D j + 2 : ℕ) : ℤ) := by positivity
    rw [Int.fdiv_eq_ediv, if_pos (Or.inl hb.le), sub_zero] at e
    have hk := kaLast τ i hi
    have hTT := Nat.mul_le_mul hT2 (le_refl Tn)
    constructor
    · have : (1 : ℤ) ≤ (wL.aP τ i : ℤ) := by
        rw [e, Int.le_ediv_iff_mul_le hb]
        have hk' : ((2 * Tn * Tn : ℕ) : ℤ) ≤ (ka.aP τ i : ℤ) := by exact_mod_cast hk
        have hTT' : ((2 * Tn : ℕ) : ℤ) ≤ ((Tn * Tn : ℕ) : ℤ) := by exact_mod_cast hTT
        have hDnW' : (((WeightFamilies.dimY D j + 2) * nW + 2 * D.R.r : ℕ) : ℤ) ≤ (Tn : ℤ) := by exact_mod_cast hDnW
        have hDT' : ((WeightFamilies.dimY D j : ℕ) : ℤ) ≤ (Tn : ℤ) := by exact_mod_cast hDT
        push_cast at hk' hTT' hDnW' hDT' ⊢
        nlinarith
      exact_mod_cast this
    · rw [e]
      exact Int.mul_ediv_self_le hb.ne'
  have wFLast : ∀ τ (i : Fin (D.R.sigW j).1), i.1 + 1 = (D.R.sigW j).1 → 1 ≤ wF.aP τ i := by
    intro τ i hi
    obtain ⟨_, h2⟩ := wLLast τ i hi
    have e := hFP τ i
    have h0' : (0 : ℤ) ≤ (WeightFamilies.dimY D j : ℤ) * wL.aP τ i := by positivity
    have h1' : (0 : ℤ) ≤ (WeightFamilies.dimY D j : ℤ) * nW := by positivity
    have h40' : (40 : ℤ) ≤ nW := by exact_mod_cast h40n
    have : (1 : ℤ) ≤ (wF.aP τ i : ℤ) := by
      push_cast at h2
      nlinarith
    exact_mod_cast this
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl
    · refine ⟨leKa _ (fun τ i => ?_) (fun τ i => ?_), ?_, ?_, ?_⟩
      · have := Nat.mul_le_mul hT1 (le_refl (w.aP τ i)); rw [kaP]; omega
      · have := Nat.mul_le_mul hT1 (le_refl (w.aM τ i)); rw [kaM]; omega
      · have := Nat.mul_le_mul hT1 (le_refl nW); rw [kan, hLn]; omega
      · rw [hLn]; omega
      · intro τ i hi; exact (wLLast τ i hi).1
    · refine ⟨leKa _ (fun τ i => ?_) (fun τ i => ?_), ?_, ?_, ?_⟩
      · rw [kaP]; omega
      · rw [kaM]; omega
      · rw [kan, hFn]; omega
      · rw [hFn]; omega
      · intro τ i hi; exact wFLast τ i hi
    · refine ⟨leKa _ (fun τ i => ?_) (fun τ i => ?_), ?_, ?_, ?_⟩
      · have := Nat.mul_le_mul hDT (le_refl (wL.aP τ i)); rw [kaP, f0P]; omega
      · have := Nat.mul_le_mul hDT (le_refl (wL.aM τ i)); rw [kaM, f0M]; omega
      · have := Nat.mul_le_mul hDT (le_refl nW); rw [kan, f0n, hFn, hLn]; omega
      · rw [f0n, hFn]; omega
      · intro τ i hi
        have := wFLast τ i hi
        rw [f0P]; omega
    · refine ⟨le_refl _, le_refl _, ?_, ?_⟩
      · rw [kan]; omega
      · intro τ i hi
        have := kaLast τ i hi
        have hTT := Nat.mul_le_mul hT2 hT1
        have e : 2 * Tn * Tn = 2 * (Tn * Tn) := by ring
        omega
  · intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · rw [hFn]; omega
    · rw [f0n, hFn]; omega
    · rw [kan]; omega
  · intro w2 hw2
    obtain ⟨h2n, h2P, h2M⟩ := hw2
    have bP : ∀ τ i, w2.aP τ i ≤ (WeightFamilies.dimY D j + 4) * wL.aP τ i := fun τ i => by
      have := h2P τ i; omega
    have bM : ∀ τ i, w2.aM τ i ≤ (WeightFamilies.dimY D j + 4) * wL.aM τ i := fun τ i => by
      have := h2M τ i; omega
    have bn : w2.n ≤ (WeightFamilies.dimY D j + 4) * wL.n := by omega
    refine ⟨leKa _ (fun τ i => ?_) (fun τ i => ?_), ?_, ?_⟩
    · have := Nat.mul_le_mul hD4 (le_refl (wL.aP τ i)); have := bP τ i; rw [kaP]; omega
    · have := Nat.mul_le_mul hD4 (le_refl (wL.aM τ i)); have := bM τ i; rw [kaM]; omega
    · have := Nat.mul_le_mul hD4 (le_refl nW); rw [kan]; rw [hLn] at bn; omega
    · have := size_le_mul w2 wL (WeightFamilies.dimY D j + 4) (by omega) bP bM bn
      push_cast at this
      exact this
  · intro w1 hw1
    obtain ⟨h1n, h1P, h1M⟩ := hw1
    have bn : w1.n ≤ 2 * wL.n := by omega
    refine ⟨leKa _ (fun τ i => ?_) (fun τ i => ?_), ?_, ?_⟩
    · have := Nat.mul_le_mul hT2 (le_refl (wL.aP τ i)); have := h1P τ i; rw [kaP]; omega
    · have := Nat.mul_le_mul hT2 (le_refl (wL.aM τ i)); have := h1M τ i; rw [kaM]; omega
    · have := Nat.mul_le_mul hT2 (le_refl nW); rw [kan]; rw [hLn] at bn; omega
    · have := size_le_mul w1 wL 2 (by norm_num) (fun τ i => (h1P τ i).le) (fun τ i => (h1M τ i).le) bn
      push_cast at this
      exact this

end GlobalTheory.RunWeights
