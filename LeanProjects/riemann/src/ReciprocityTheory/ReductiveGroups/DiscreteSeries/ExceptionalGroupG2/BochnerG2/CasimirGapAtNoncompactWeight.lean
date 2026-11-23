import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CasimirGapAtNoncompactWeight
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.LayerBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.BochIneq
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CrossOpSlotBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.NcVOneDecomp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CrossOpEigGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.Numerics
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.KhwEqZeroSharp

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}

section Unitary

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {lam : Fin n → ℝ} {V : Submodule ℂ M}

theorem k_highest_weight_layer_decomp (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : 2 * (n : ℝ) < h) {μ : Fin n → ℝ} {w : M}
    (hw : w ∈ genSub E V) (hμ : IsKHWVec ε E μ w) :
    ∃ w₀ ∈ V, IsKHWVec ε E μ w₀ ∧ ∃ m, ∃ ws : Fin m → M, w = w₀ + ∑ j, ws j ∧
      ∀ j : Fin m, ws j ∈ layer ε E V ((j : ℕ) + 1) ∧ (ws j ≠ 0 →
        IsNCSum ε ((j : ℕ) + 1) (μ - lowK ε lam) ∧ 0 < h - n + 1 ∧
        casValK ε (lowK ε lam) + 2 * (((j : ℕ) : ℝ) + 1) * (h - n + 1) ≤ casValK ε μ) := by
  obtain ⟨m, hm⟩ := exists_layer_of_mem_genSub hE hV.2.1 hw
  obtain ⟨w₀, hw₀, hw₀μ, ws, hsum, hws⟩ := layer_khw_decomp hE hU hV.1 hV.2.1 hm hμ
  refine ⟨w₀, hw₀, hw₀μ, m, ws, hsum, fun j => ⟨(hws j).1, fun h0 => ?_⟩⟩
  obtain ⟨h1, h2⟩ := khw_layer_succ_bound hE hU hV hc hmono hh hbig (j : ℕ) (hws j).1
    (hws j).2.1 h0 (hws j).2.2
  obtain ⟨a, b, hab⟩ := isNCSum_succ_exists h1
  have := (gap_gt hab hbig).2
  exact ⟨h1, by linarith, h2⟩

theorem casimir_gap_at_noncompact_weight (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : 2 * (n : ℝ) < h) {μ : Fin n → ℝ} {w : M}
    (hw : w ∈ genSub E V) (hw0 : w ≠ 0) (hμ : IsKHWVec ε E μ w) (hne : μ ≠ lowK ε lam) :
    ∃ j : ℕ, IsNCSum ε (j + 1) (μ - lowK ε lam) ∧ 0 < h - n + 1 ∧
      casValK ε (lowK ε lam) + 2 * ((j : ℝ) + 1) * (h - n + 1) ≤ casValK ε μ := by
  obtain ⟨w₀, hw₀, -, m, ws, hwsum, hws⟩ := k_highest_weight_layer_decomp hE hU hV hc hmono hh hbig hw hμ
  by_cases hall : ∀ j, ws j = 0
  · exfalso
    have hweq : w = w₀ := by
      rw [hwsum]
      simp [hall]
    have hwV : w ∈ V := by
      rw [hweq]
      exact hw₀
    exact hne (khw_weight_eq_of_irr hE hV hwV hw0 hμ)
  · push_neg at hall
    obtain ⟨j, hj⟩ := hall
    obtain ⟨h1, h2, h3⟩ := (hws j).2 hj
    exact ⟨(j : ℕ), h1, h2, h3⟩

theorem khw_lowK_mem (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hgap : StdGap ε lam) {w : M} (hw : w ∈ genSub E V) (hμ : IsKHWVec ε E (lowK ε lam) w) :
    w ∈ V := by
  obtain ⟨hmono, h, hh, hbig⟩ := hgap
  obtain ⟨w₀, hw₀, -, m, ws, rfl, hws⟩ := k_highest_weight_layer_decomp hE hU hV hc hmono hh hbig hw hμ

  have hzero : ∀ j, ws j = 0 := by
    intro j
    by_contra hne
    obtain ⟨-, hpos, hle⟩ := (hws j).2 hne
    have h1 : (0 : ℝ) < 2 * (((j : ℕ) : ℝ) + 1) := by positivity
    have h2 := mul_pos h1 hpos
    linarith
  simpa [hzero] using hw₀

theorem vogan_min (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hgap : StdGap ε lam) {μ : Fin n → ℝ} {w : M} (hw : w ∈ genSub E V) (hw0 : w ≠ 0)
    (hμ : IsKHWVec ε E μ w) :
    nsq (lowK ε lam + (2 : ℝ) • rhoC ε) ≤ nsq (μ + (2 : ℝ) • rhoC ε) := by
  by_cases hne : μ = lowK ε lam
  · subst hne
    exact le_refl _
  obtain ⟨hmono, h, hh, hbig⟩ := hgap
  obtain ⟨j, ⟨γ, -, hsum⟩, -, hle⟩ := casimir_gap_at_noncompact_weight hE hU hV hc hmono hh hbig hw hw0 hμ hne
  have hexp : ∀ x : Fin n → ℝ, nsq (x + (2 : ℝ) • rhoC ε) =
      nsq (x + rhoC ε) + 2 * dot x (rhoC ε) + 3 * nsq (rhoC ε) := by
    intro x
    simp only [nsq, dot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  have hlin : dot μ (rhoC ε) - dot (lowK ε lam) (rhoC ε) = dot (μ - lowK ε lam) (rhoC ε) := by
    simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  have hroot : ∀ a b : Fin n, dot (root a b) (rhoC ε) = rhoC ε a - rhoC ε b := by
    intro a b
    simp [dot, root, Pi.single_apply, sub_mul, ite_mul, Finset.sum_sub_distrib]
  have hdsum : dot (μ - lowK ε lam) (rhoC ε) = ∑ i, (rhoC ε (γ i).1 - rhoC ε (γ i).2) := by
    rw [hsum]
    simp only [dot, Finset.sum_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => hroot _ _

  have hρ : ∀ a, -((n : ℝ) / 2) ≤ rhoC ε a ∧ rhoC ε a ≤ (n : ℝ) / 2 := by
    have key : ∀ s t : Finset (Fin n),
        -((n : ℝ) / 2) ≤ ((s.card : ℝ) - t.card) / 2 ∧ ((s.card : ℝ) - t.card) / 2 ≤ (n : ℝ) / 2 := by
      intro s t
      have hs : (s.card : ℝ) ≤ n := by exact_mod_cast (card_le_univ s).trans (by simp)
      have ht : (t.card : ℝ) ≤ n := by exact_mod_cast (card_le_univ t).trans (by simp)
      have hs0 : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
      have ht0 : (0 : ℝ) ≤ t.card := Nat.cast_nonneg _
      constructor <;> linarith
    intro a
    exact key _ _
  have hterm : ∀ i : Fin (j + 1), -(n : ℝ) ≤ rhoC ε (γ i).1 - rhoC ε (γ i).2 := by
    intro i
    obtain ⟨h1, -⟩ := hρ (γ i).1
    obtain ⟨-, h2⟩ := hρ (γ i).2
    linarith
  have hdot : -(((j : ℝ) + 1) * n) ≤ dot (μ - lowK ε lam) (rhoC ε) := by
    rw [hdsum]
    have hc : ∑ _i : Fin (j + 1), (-(n : ℝ)) = -(((j : ℝ) + 1) * n) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    rw [← hc]
    exact Finset.sum_le_sum fun i _ => hterm i
  have hprod : 0 ≤ ((j : ℝ) + 1) * (h - 2 * n + 1) := by
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    exact mul_nonneg (by linarith) (by linarith)
  simp only [casValK] at hle
  have e1 := hexp μ
  have e2 := hexp (lowK ε lam)
  linarith

theorem khw_mem_layer (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hgap : StdGap ε lam) (μ : Fin n → ℝ) :
    ∃ k : ℕ, ∀ w ∈ genSub E V, IsKHWVec ε E μ w → w ∈ layer ε E V k := by
  obtain ⟨hmono, h, hh, hbig⟩ := hgap
  have hn : (0 : ℝ) < h - n + 1 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hmon : Monotone (layer ε E V) := by
    refine monotone_nat_of_le_succ fun k => ?_
    simp only [layer]
    exact le_sup_left
  refine ⟨⌈(casValK ε μ - casValK ε (lowK ε lam)) / (2 * (h - n + 1))⌉₊, fun w hw hμ => ?_⟩
  obtain ⟨w₀, hw₀, -, m, ws, rfl, hws⟩ := k_highest_weight_layer_decomp hE hU hV hc hmono hh hbig hw hμ
  refine add_mem (hmon (Nat.zero_le _) (show w₀ ∈ layer ε E V 0 from hw₀))
    (_root_.sum_mem fun j _ => ?_)
  by_cases hj : ws j = 0
  · rw [hj]
    exact zero_mem _
  · obtain ⟨hmem, hrest⟩ := hws j
    obtain ⟨-, -, hle⟩ := hrest hj
    refine hmon ?_ hmem

    have hq : (((j : ℕ) : ℝ) + 1) ≤ (casValK ε μ - casValK ε (lowK ε lam)) / (2 * (h - n + 1)) := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    have hq' := hq.trans (Nat.le_ceil _)
    exact_mod_cast hq'

theorem admissible (hE : IsGlRep E) (hU : IsInfUnitary ε E)
    (hV : IsKIrrHW ε E (lowK ε lam) V) (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hgap : StdGap ε lam) (μ : Fin n → ℝ) :
    ∃ S : Submodule ℂ M, FiniteDimensional ℂ S ∧ S ≤ genSub E V ∧ IsKStableSub ε E S ∧
      ∀ w ∈ genSub E V, IsKHWVec ε E μ w → w ∈ S := by
  obtain ⟨k, hk⟩ := khw_mem_layer hE hU hV hc hgap μ
  obtain ⟨hfd, hks, -, -⟩ := hV
  have hcl : ∀ a b, ∀ v ∈ genSub E V, E a b v ∈ genSub E V := by
    intro a b v hv
    rw [genSub, Submodule.mem_sInf] at hv ⊢
    exact fun T hT => hT.2 a b v (hv T hT)
  have hgen : ∀ j, layer ε E V j ≤ genSub E V := by
    intro j
    induction j with
    | zero =>
      simp only [layer]
      rw [genSub]
      exact le_sInf fun T hT => hT.1
    | succ j ih =>
      simp only [layer]
      refine sup_le ih (iSup_le fun a => iSup_le fun b => iSup_le fun _ => ?_)
      rw [Submodule.map_le_iff_le_comap]
      intro v hv
      exact hcl a b v (ih hv)
  exact ⟨layer ε E V k, finiteDimensional_layer hfd k, hgen k, layer_kStable hE hks k, hk⟩

end Unitary

end ReciprocityTheory.ChartRestriction.DS.G2
