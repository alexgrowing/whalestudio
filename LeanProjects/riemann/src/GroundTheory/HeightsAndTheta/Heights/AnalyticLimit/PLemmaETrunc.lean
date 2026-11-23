import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETrunc
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PListProductMass
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaETruncSmooth
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open ReciprocityTheory.AnForm.A (regMax tmax regMax_thm)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh isPotentialAdd isPotential_ofFun
  st_smooth_continuous)

theorem LemmaETrunc.proof : LemmaETrunc.Statement := by
  intro D X _ A Om Yo r C₁ u hYo hd hr hC hu hnn hu0 hlow hcase R hR
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = -(C₁ * Real.log R + 2) + 1 := ⟨_, rfl⟩
  have hlogR : 1 ≤ Real.log R := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hR
  have hCR : 0 ≤ C₁ * Real.log R := mul_nonneg hC (by linarith)
  obtain ⟨-, -, -, hbd, hfix, -⟩ := (regMax_thm (Fin 2)).1 1 one_pos

  have hb : ∀ a : ℝ, a ≤ 0 →
      -(C₁ * Real.log R + 2) ≤ regMax 1 ![a, c] - 1 ∧ regMax 1 ![a, c] - 1 ≤ 0 := by
    intro a ha
    obtain ⟨h1, h2⟩ := hbd ![a, c]
    have hc1 : (![a, c] : Fin 2 → ℝ) 1 ≤ tmax ![a, c] := by
      unfold tmax
      exact Finset.le_sup' _ (Finset.mem_univ _)
    have hc2 : tmax ![a, c] ≤ 0 := by
      unfold tmax
      refine Finset.sup'_le _ _ fun i _ => ?_
      fin_cases i
      · simpa using ha
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        linarith
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hc1
    constructor <;> linarith

  have hfixU : ∀ a : ℝ, c + 1 ≤ a → regMax 1 ![a, c] = a := fun a ha => by
    have := hfix ![a, c] 0 fun j hj => by
      fin_cases j
      · simp at hj
      · simpa using ha
    simpa using this
  have hfixC : ∀ a : ℝ, a + 1 ≤ c → regMax 1 ![a, c] = c := fun a ha => by
    have := hfix ![a, c] 1 fun j hj => by
      fin_cases j
      · simpa using ha
      · simp at hj
    simpa using this
  have hnear : ∀ x ∈ Yo, r x < R → c + 1 ≤ u x := by
    intro x hx hxR
    have h1 : Real.log (r x) ≤ Real.log R :=
      Real.log_le_log (lt_of_lt_of_le (Real.exp_pos 1) (hr x hx)) hxR.le
    have h2 := mul_le_mul_of_nonneg_left h1 hC
    have h3 := hlow x hx
    rw [hc]
    linarith
  rcases hcase with hsm | hpole
  ·
    have hle : ∀ x, u x ≤ 0 := by
      have hcl : closure Yo ⊆ {x | u x ≤ 0} :=
        closure_minimal hu0 (isClosed_le (st_smooth_continuous A hsm) continuous_const)
      intro x
      exact hcl (hd.closure_eq ▸ Set.mem_univ x)
    have hpot : IsPotential A (potForm Om.pot u) :=
      isPotentialAdd A _ _ Om.isPot (isPotential_ofFun A u hsm)
    have hint : interior Yoᶜ = ∅ := by
      rw [interior_compl, hd.closure_eq, Set.compl_univ]
    have hpsh := isPsh_of_formNonneg hint hpot hnn
    have hnnU : FormNonneg A Set.univ (potForm Om.pot u) := fun x k y hy w =>
      hpsh x k y ⟨hy.1, hy.2.2⟩ w
    obtain ⟨hs, hp⟩ := trunc_smooth_psh A Om isOpen_univ hsm hnnU c one_pos
      (fun p => regMax 1 ![u p, c] - 1) (fun _ _ => rfl) (fun p hp => absurd (Set.mem_univ p) hp)
    refine ⟨_, hs, hp, fun x => hb (u x) (hle x), -1, fun x hx hxR => ?_⟩
    show regMax 1 ![u x, c] - 1 = u x + -1
    rw [hfixU _ (hnear x hx hxR)]
    ring
  ·
    classical
    let v : X → ℝ := fun p => if p ∈ Yo then regMax 1 ![u p, c] - 1 else c - 1
    have hvC : ∀ p ∉ Yo, ∃ N : Set X, IsOpen N ∧ p ∈ N ∧ ∃ κ : ℝ, ∀ q ∈ N, v q = κ := by
      intro p hp
      have hev : ∀ᶠ q in 𝓝[Yo] p, u q ≤ c - 1 := tendsto_atBot.1 (hpole p hp) (c - 1)
      obtain ⟨N, hN, hpN, hNs⟩ := mem_nhdsWithin.1 hev
      refine ⟨N, hN, hpN, c - 1, fun q hq => ?_⟩
      by_cases hqY : q ∈ Yo
      · have hq' : u q ≤ c - 1 := hNs ⟨hq, hqY⟩
        simp only [v, if_pos hqY]
        rw [hfixC _ (by linarith)]
      · simp only [v, if_neg hqY]
    obtain ⟨hs, hp⟩ := trunc_smooth_psh A Om hYo hu hnn c one_pos v
      (fun p hp => by simp only [v, if_pos hp]) hvC
    refine ⟨v, hs, hp, fun x => ?_, -1, fun x hx hxR => ?_⟩
    · by_cases hx : x ∈ Yo
      · simp only [v, if_pos hx]
        exact hb _ (hu0 x hx)
      · simp only [v, if_neg hx]
        constructor <;> linarith
    · simp only [v, if_pos hx]
      rw [hfixU _ (hnear x hx hxR)]
      ring

end GroundTheory.Heights₂.Heights.AnalyticLimit
