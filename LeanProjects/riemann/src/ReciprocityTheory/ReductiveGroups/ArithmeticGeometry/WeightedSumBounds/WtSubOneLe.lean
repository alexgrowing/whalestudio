import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.TypicalCurveStructureConstants
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.CoeffLgPcurveTop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.GeomSumRoot

namespace ReciprocityTheory.ChartRestriction.G.Sh

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh.PTb

noncomputable section

theorem pt6' : TypicalCurveRebasing := by
  unfold TypicalCurveRebasing
  intro C _ _ _ v p hp hv d m G γ x hc hx
  dsimp only
  have hcr : ∀ u, IsCurve v (rescaleCurve (x u) (γ u)) := fun u => isCurve_rescale (hx u) (hc u)
  have hγ' : IsCurve v (G.sumF fun u => rescaleCurve (x u) (γ u)) := isCurve_sumF G _ hcr
  have hlc : ∀ (k : ℕ) (a : Fin d),
      PowerSeries.coeff k (G.lgCurve (G.sumF fun u => rescaleCurve (x u) (γ u)) a) =
        ∑ u, x u ^ k * PowerSeries.coeff k (G.lgCurve (γ u) a) := by
    intro k a
    rw [lgCurve_sumF G _ hcr a, map_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [lgCurve_rescale G (x u) (fun b => (hc u b).1) a, PowerSeries.coeff_rescale]
  have hL : ∀ n : ℕ, G.lc p (G.sumF fun u => rescaleCurve (x u) (γ u)) n =
      ∑ u, x u ^ p ^ n • G.lc p (γ u) n := by
    intro n
    funext a
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, LogFGL.lc]
    exact hlc (p ^ n) a
  refine ⟨hγ', ?_, hL, ?_⟩
  · rw [tangent_eq_lc_zero G p (fun b => (hγ' b).1), hL 0]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [tangent_eq_lc_zero G p (fun b => (hc u b).1), pow_zero, pow_one]
  · intro hT
    unfold LogFGL.IsPTypical at hT ⊢
    intro a k hk
    rw [hlc k a]
    refine Finset.sum_eq_zero fun u _ => ?_
    rw [hT u a k hk, mul_zero]

theorem pt5' : TypicalCurveStructureConstants := by
  intro C _ _ _ v p hp hv d h ty G γ hB
  obtain ⟨hγ, hγty, hdet⟩ := hB
  have hdet' : v (tmat γ).det = 0 := hdet
  have : NeZero (p : C) := ⟨Nat.cast_ne_zero.2 hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C p
  choose δ hδc hδlg using fun a => exists_average G hp hζ (hγ a)
  have hlcδ : ∀ a n, G.lc p (δ a) n = (p : C) • G.lc p (γ a) (n + 1) := by
    intro a n
    funext c
    simp only [LogFGL.lc, Pi.smul_apply, smul_eq_mul]
    rw [hδlg, pow_succ']
  have hδt : ∀ a, G.IsOfType p ty (ty a + 1) (δ a) := by
    intro a
    refine ⟨fun c j hj => ?_, fun n c hc => ?_⟩
    · rw [hδlg, (hγty a).1 c (p * j) (fun k hk => ?_), mul_zero]
      rcases k with _ | k
      · rw [pow_zero] at hk
        exact hp.one_lt.ne' (Nat.eq_one_of_mul_eq_one_right hk)
      · exact hj k (by rw [pow_succ'] at hk; exact Nat.eq_of_mul_eq_mul_left hp.pos hk)
    · rw [hlcδ]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [(hγty a).2 (n + 1) c (by intro e; apply hc; rw [e]; push_cast; ring), mul_zero]
  refine ⟨fun s b a => ptx G p γ (δ a) s b,
    fun s b a => ptx_int G hp hγ (fun b => (hγty b).1) hdet' (δ a) (hδc a) (hδt a).1 s b,
    fun s b a hne => ?_, fun a n => ?_⟩
  · rw [ptx_type ty G hp hγ hdet' hγty (δ a) _ (hδt a) s b hne]
    ring
  · rw [← hlcδ a n, ptx_rel G p hγ hdet' (δ a) n]
    refine (Finset.sum_range_reflect _ (n + 1)).symm.trans ?_
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmn : m ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    dsimp only
    rw [show n + 1 - 1 - m = n - m by omega, Nat.sub_sub_self hmn]

theorem wt_sub_one_le {r : ℝ} {y : WithTop ℝ} (h : (r : WithTop ℝ) ≤ 1 + y) :
    ((r - 1 : ℝ) : WithTop ℝ) ≤ y := by
  induction y using WithTop.recTopCoe with
  | top => exact le_top
  | coe a =>
    have h1 : ((1 : WithTop ℝ) + (a : WithTop ℝ)) = ((1 + a : ℝ) : WithTop ℝ) := by
      norm_cast
    rw [h1, WithTop.coe_le_coe] at h
    exact WithTop.coe_le_coe.mpr (by linarith)

private theorem le_valuation_finset_sum {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))
    {ι : Type} (s : Finset ι) (f : ι → C) (g : WithTop ℝ) (h : ∀ i ∈ s, g ≤ v (f i)) :
    g ≤ v (∑ i ∈ s, f i) := by
  classical
  revert h
  refine Finset.induction_on s (fun _ => by simp) ?_
  intro i s hi ih h
  rw [Finset.sum_insert hi]
  exact le_trans (le_min (h i (Finset.mem_insert_self i s))
    (ih fun j hj => h j (Finset.mem_insert_of_mem hj))) (AddValuation.map_add v _ _)

theorem pt5v' : TypicalCurveValuationBounds := by
  unfold TypicalCurveValuationBounds
  intro C _ _ _ v p hp hv d h ty G γ hB a
  obtain ⟨sc, hsc, -, hrec⟩ := pt5' C v p hp hv d h ty G γ hB
  obtain ⟨hcur, -, hdet⟩ := hB
  have H1 : ∀ (n : ℕ) (b c : Fin d), (((-(n : ℝ)) : ℝ) : WithTop ℝ) ≤ v (G.lc p (γ b) n c) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro n ih b c
    rcases n with _ | n
    · rw [← tangent_eq_lc_zero G p (fun e => (hcur b e).1)]
      have h0 : (0 : WithTop ℝ) ≤ v (tangent (γ b) c) := (hcur b c).2 1
      have e0 : (((-((0 : ℕ) : ℝ)) : ℝ) : WithTop ℝ) = 0 := by simp
      rw [e0]
      exact h0
    · have hr := congrFun (hrec b n) c
      simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at hr
      have hge : (((-(n : ℝ)) : ℝ) : WithTop ℝ) ≤ v ((p : C) * G.lc p (γ b) (n + 1) c) := by
        rw [hr]
        apply le_valuation_finset_sum
        intro m hm
        apply le_valuation_finset_sum
        intro e _
        rw [AddValuation.map_mul, AddValuation.map_pow]
        have hm' : m < n + 1 := Finset.mem_range.mp hm
        have h1 : (0 : WithTop ℝ) ≤ (p ^ m) • v (sc (n - m) e b) := nsmul_nonneg (hsc _ _ _) _
        have h2 := ih m hm' e c
        have h3 : (((-(n : ℝ)) : ℝ) : WithTop ℝ) ≤ (((-(m : ℝ)) : ℝ) : WithTop ℝ) := by
          apply WithTop.coe_le_coe.mpr
          have : (m : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp hm'
          linarith
        calc (((-(n : ℝ)) : ℝ) : WithTop ℝ) = 0 + (((-(n : ℝ)) : ℝ) : WithTop ℝ) := (zero_add _).symm
          _ ≤ (p ^ m) • v (sc (n - m) e b) + v (G.lc p (γ e) m c) := add_le_add h1 (h3.trans h2)
      rw [AddValuation.map_mul, hv] at hge
      have := wt_sub_one_le hge
      convert this using 2
      push_cast
      ring
  refine ⟨fun n c => H1 n a c, ?_⟩
  intro h1 n c hn
  have hne : Matrix.det (Matrix.of fun a b => tangent (γ a) b) ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hdet
    simp at hdet
  have hs0 : ∀ e, sc 0 e a = 0 := by
    have hr := hrec a 0
    simp only [zero_add] at hr
    rw [h1, smul_zero, Finset.sum_range_one] at hr
    simp only [tsub_zero, pow_zero, pow_one] at hr
    have hM : Matrix.vecMul (fun e => sc 0 e a) (Matrix.of fun e b => tangent (γ e) b) = 0 := by
      funext b
      have hb := congrFun hr b
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hb
      simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply]
      refine Eq.trans ?_ hb.symm
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [tangent_eq_lc_zero G p (fun f => (hcur e f).1)]
    intro e
    exact congrFun (Matrix.eq_zero_of_vecMul_eq_zero hne hM) e
  obtain _ | _ | k := n
  · omega
  · have h10 : G.lc p (γ a) (0 + 1) c = 0 := by simp [h1]
    rw [h10, AddValuation.map_zero]
    exact le_top
  · have hr := congrFun (hrec a (k + 1)) c
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at hr
    have hge : (((-(k : ℝ)) : ℝ) : WithTop ℝ) ≤ v ((p : C) * G.lc p (γ a) (k + 1 + 1) c) := by
      rw [hr]
      apply le_valuation_finset_sum
      intro m hm
      apply le_valuation_finset_sum
      intro e _
      have hm' : m < k + 1 + 1 := Finset.mem_range.mp hm
      rcases Nat.lt_succ_iff_lt_or_eq.mp hm' with hlt | heq
      · rw [AddValuation.map_mul, AddValuation.map_pow]
        have h1' : (0 : WithTop ℝ) ≤ (p ^ m) • v (sc (k + 1 - m) e a) := nsmul_nonneg (hsc _ _ _) _
        have h2 := H1 m e c
        have h3 : (((-(k : ℝ)) : ℝ) : WithTop ℝ) ≤ (((-(m : ℝ)) : ℝ) : WithTop ℝ) := by
          apply WithTop.coe_le_coe.mpr
          have : (m : ℝ) ≤ k := by exact_mod_cast Nat.lt_succ_iff.mp hlt
          linarith
        calc (((-(k : ℝ)) : ℝ) : WithTop ℝ) = 0 + (((-(k : ℝ)) : ℝ) : WithTop ℝ) := (zero_add _).symm
          _ ≤ (p ^ m) • v (sc (k + 1 - m) e a) + v (G.lc p (γ e) m c) := add_le_add h1' (h3.trans h2)
      · subst heq
        rw [Nat.sub_self, hs0 e, zero_pow (pow_ne_zero _ hp.ne_zero), zero_mul, AddValuation.map_zero]
        exact le_top
    rw [AddValuation.map_mul, hv] at hge
    have := wt_sub_one_le hge
    convert this using 2
    push_cast
    ring

end

end ReciprocityTheory.ChartRestriction.G.Sh
