import Mathlib
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.JetOfMonomialSumStatement
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

namespace JetOfMonomialSum

open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {x : E}

theorem analyticAt_fderiv_apply {f : E → ℂ} (hf : AnalyticAt ℂ f x) (w : E) :
    AnalyticAt ℂ (fun y => fderiv ℂ f y w) x :=
  ((ContinuousLinearMap.apply ℂ ℂ w).analyticAt _).comp hf.fderiv

theorem vanish_one {f : E → ℂ} (h : f x = 0) : ∀ k < 1, iteratedFDeriv ℂ k f x = 0 := by
  intro k hk
  obtain rfl : k = 0 := by omega
  ext m
  simp [iteratedFDeriv_zero_apply, h]

theorem vanish_mul {f g : E → ℂ} (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x) {a b : ℕ}
    (hfa : ∀ k < a, iteratedFDeriv ℂ k f x = 0) (hgb : ∀ k < b, iteratedFDeriv ℂ k g x = 0) :
    ∀ k < a + b, iteratedFDeriv ℂ k (fun y => f y * g y) x = 0 := by
  intro k hk
  obtain ⟨s, hs, hso, hxs⟩ :=
    eventually_nhds_iff.1 (hf.eventually_analyticAt.and hg.eventually_analyticAt)
  have hfs : ContDiffOn ℂ ⊤ f s := fun y hy => (hs y hy).1.contDiffAt.contDiffWithinAt
  have hgs : ContDiffOn ℂ ⊤ g s := fun y hy => (hs y hy).2.contDiffAt.contDiffWithinAt
  have key := norm_iteratedFDerivWithin_mul_le hfs hgs hso.uniqueDiffOn hxs (n := k) le_top
  rw [iteratedFDerivWithin_of_isOpen k hso hxs] at key
  have hsum : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDerivWithin ℂ i f s x‖ *
      ‖iteratedFDerivWithin ℂ (k - i) g s x‖ = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hik := Finset.mem_range.1 hi
    rw [iteratedFDerivWithin_of_isOpen i hso hxs, iteratedFDerivWithin_of_isOpen (k - i) hso hxs]
    rcases lt_or_ge i a with h | h
    · simp [hfa i h]
    · simp [hgb (k - i) (by omega)]
  rw [hsum] at key
  exact norm_le_zero_iff.1 key

theorem top_mul {f g : E → ℂ} (hf : AnalyticAt ℂ f x) (hg : AnalyticAt ℂ g x) {a : ℕ}
    (hfa : ∀ k < a, iteratedFDeriv ℂ k f x = 0) :
    iteratedFDeriv ℂ a (fun y => f y * g y) x = g x • iteratedFDeriv ℂ a f x := by
  have hg' : AnalyticAt ℂ (fun y => g y - g x) x := hg.sub analyticAt_const
  have e : (fun y => f y * g y) = (fun y => f y * (g y - g x)) + (fun y => g x • f y) := by
    funext y
    simp only [Pi.add_apply, smul_eq_mul]
    ring
  rw [e, iteratedFDeriv_add_apply (hf.fun_mul hg').contDiffAt
      (analyticAt_const.fun_smul hf).contDiffAt,
    vanish_mul hf hg' hfa (vanish_one (by simp)) a (by omega), zero_add]
  exact iteratedFDeriv_const_smul_apply' hf.contDiffAt

theorem iteratedFDeriv_fderiv_apply {f : E → ℂ} (hf : AnalyticAt ℂ f x) (w : E) (k : ℕ)
    (m : Fin k → E) :
    iteratedFDeriv ℂ k (fun y => fderiv ℂ f y w) x m =
      iteratedFDeriv ℂ (k + 1) f x (Fin.snoc m w : Fin (k + 1) → E) := by
  rw [iteratedFDeriv_succ_apply_right, Fin.init_snoc, Fin.snoc_last]
  have := (ContinuousLinearMap.apply ℂ ℂ w).iteratedFDeriv_comp_left
    (hf.fderiv.contDiffAt (n := ⊤)) (i := k) le_top
  exact congrArg (fun L => L m) this

theorem snoc_const {F : Type*} (k : ℕ) (w : F) :
    (Fin.snoc (fun _ : Fin k => w) w : Fin (k + 1) → F) = fun _ => w := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem iteratedFDeriv_fderiv_diag {f : E → ℂ} (hf : AnalyticAt ℂ f x) (w : E) (k : ℕ) :
    iteratedFDeriv ℂ k (fun y => fderiv ℂ f y w) x (fun _ => w) =
      iteratedFDeriv ℂ (k + 1) f x (fun _ => w) := by
  rw [iteratedFDeriv_fderiv_apply hf, snoc_const]

theorem step {g v : E → ℂ} (hg : AnalyticAt ℂ g x) (hv : AnalyticAt ℂ v x) {a : ℕ}
    (hga : ∀ k < a, iteratedFDeriv ℂ k g x = 0) (w : E) :
    iteratedFDeriv ℂ (a + 1) (fun y => g y * v y) x (fun _ => w) =
      fderiv ℂ v x w * iteratedFDeriv ℂ a g x (fun _ => w) +
        iteratedFDeriv ℂ a (fun y => v y * fderiv ℂ g y w) x (fun _ => w) := by
  have hgv : AnalyticAt ℂ (fun y => g y * v y) x := hg.fun_mul hv
  rw [← iteratedFDeriv_fderiv_diag hgv]
  have heq : (fun y => fderiv ℂ (fun y => g y * v y) y w) =ᶠ[𝓝 x]
      fun y => g y * fderiv ℂ v y w + v y * fderiv ℂ g y w := by
    filter_upwards [hg.eventually_analyticAt, hv.eventually_analyticAt] with y hgy hvy
    rw [fderiv_fun_mul hgy.differentiableAt hvy.differentiableAt]
    simp [smul_eq_mul]
  have h1 := analyticAt_fderiv_apply hv w
  have h2 := analyticAt_fderiv_apply hg w
  rw [(heq.iteratedFDeriv ℂ a).eq_of_nhds,
    fun_iteratedFDeriv_add_apply (hg.fun_mul h1).contDiffAt (hv.fun_mul h2).contDiffAt,
    top_mul hg h1 hga]
  simp [smul_eq_mul]

theorem order_one {v : E → ℂ} (hv : AnalyticAt ℂ v x) (hv0 : v x = 0) (w : E) :
    ∀ (a : ℕ) (g : E → ℂ), AnalyticAt ℂ g x → (∀ k < a, iteratedFDeriv ℂ k g x = 0) →
      iteratedFDeriv ℂ (a + 1) (fun y => g y * v y) x (fun _ => w) =
        ((a : ℂ) + 1) * iteratedFDeriv ℂ a g x (fun _ => w) * fderiv ℂ v x w := by
  intro a
  induction a with
  | zero =>
    intro g hg _
    rw [step hg hv (fun k hk => absurd hk (Nat.not_lt_zero k)) w]
    simp [iteratedFDeriv_zero_apply, hv0]
    ring
  | succ a ih =>
    intro g hg hga
    have hdg := analyticAt_fderiv_apply hg w
    have hdga : ∀ k < a, iteratedFDeriv ℂ k (fun y => fderiv ℂ g y w) x = 0 := by
      intro k hk
      ext m
      rw [iteratedFDeriv_fderiv_apply hg, hga (k + 1) (by omega)]
      simp
    have e : (fun y => v y * fderiv ℂ g y w) = fun y => fderiv ℂ g y w * v y := by
      funext y
      ring
    rw [step hg hv hga w, e, ih _ hdg hdga, iteratedFDeriv_fderiv_diag hg]
    push_cast
    ring

theorem mul_pow_jet {v : E → ℂ} (hv : AnalyticAt ℂ v x) (hv0 : v x = 0) (w : E)
    {g : E → ℂ} (hg : AnalyticAt ℂ g x) {c : ℕ} (hgc : ∀ k < c, iteratedFDeriv ℂ k g x = 0)
    {G : ℂ} (hG : iteratedFDeriv ℂ c g x (fun _ => w) = c.factorial * G) (m : ℕ) :
    (∀ k < c + m, iteratedFDeriv ℂ k (fun y => g y * v y ^ m) x = 0) ∧
      iteratedFDeriv ℂ (c + m) (fun y => g y * v y ^ m) x (fun _ => w) =
        (c + m).factorial * G * fderiv ℂ v x w ^ m := by
  induction m with
  | zero => simpa using ⟨hgc, hG⟩
  | succ m ih =>
    have hgm : AnalyticAt ℂ (fun y => g y * v y ^ m) x := hg.fun_mul (hv.fun_pow m)
    have e : (fun y => g y * v y ^ (m + 1)) = fun y => (g y * v y ^ m) * v y := by
      funext y
      ring
    rw [e, ← add_assoc]
    refine ⟨vanish_mul hgm hv ih.1 (vanish_one hv0), ?_⟩
    rw [order_one hv hv0 w (c + m) _ hgm ih.1, ih.2, Nat.factorial_succ]
    push_cast
    ring

theorem prod_pow_jet {p : ℕ} (u : Fin p → E → ℂ) (hu : ∀ i, AnalyticAt ℂ (u i) x)
    (hu0 : ∀ i, u i x = 0) (α : Fin p → ℕ) (w : E) (s : Finset (Fin p)) :
    AnalyticAt ℂ (fun y => ∏ i ∈ s, u i y ^ α i) x ∧
    (∀ k < ∑ i ∈ s, α i, iteratedFDeriv ℂ k (fun y => ∏ i ∈ s, u i y ^ α i) x = 0) ∧
    iteratedFDeriv ℂ (∑ i ∈ s, α i) (fun y => ∏ i ∈ s, u i y ^ α i) x (fun _ => w) =
      (∑ i ∈ s, α i).factorial * ∏ i ∈ s, fderiv ℂ (u i) x w ^ α i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨?_, fun k hk => by simp at hk, ?_⟩
    · simp only [Finset.prod_empty]
      exact analyticAt_const
    · simp only [Finset.sum_empty, Finset.prod_empty, Nat.factorial_zero, Nat.cast_one, mul_one]
      exact iteratedFDeriv_zero_apply _
  | insert j s hj ih =>
    obtain ⟨ha, hv, hd⟩ := ih
    have e : (fun y => ∏ i ∈ insert j s, u i y ^ α i) =
        fun y => (∏ i ∈ s, u i y ^ α i) * u j y ^ α j := by
      funext y
      rw [Finset.prod_insert hj, mul_comm]
    have := mul_pow_jet (hu j) (hu0 j) w ha hv (G := ∏ i ∈ s, fderiv ℂ (u i) x w ^ α i) hd (α j)
    rw [e, Finset.sum_insert hj, Finset.prod_insert hj, add_comm (α j)]
    refine ⟨ha.fun_mul ((hu j).fun_pow _), this.1, ?_⟩
    rw [this.2]
    ring

theorem proof : Statement := by
  intro n p u h z₀ a hu hu0 hh
  have hP : ∀ α ∈ Finset.Nat.antidiagonalTuple p a,
      AnalyticAt ℂ (fun z => ∏ i, u i z ^ α i) z₀ ∧
      (∀ k < a, iteratedFDeriv ℂ k (fun z => ∏ i, u i z ^ α i) z₀ = 0) ∧
      ∀ w, iteratedFDeriv ℂ a (fun z => ∏ i, u i z ^ α i) z₀ (fun _ => w) =
        a.factorial * ∏ i, fderiv ℂ (u i) z₀ w ^ α i := by
    intro α hα
    rw [Finset.Nat.mem_antidiagonalTuple] at hα
    obtain ⟨h1, h2, -⟩ := prod_pow_jet u hu hu0 α 0 Finset.univ
    refine ⟨h1, hα ▸ h2, fun w => ?_⟩
    have := (prod_pow_jet u hu hu0 α w Finset.univ).2.2
    rwa [hα] at this
  have h2 : iteratedFDeriv ℂ a
      (fun z => ∑ α ∈ Finset.Nat.antidiagonalTuple p a, (∏ i, u i z ^ α i) * h α z) z₀ =
      ∑ α ∈ Finset.Nat.antidiagonalTuple p a,
        h α z₀ • iteratedFDeriv ℂ a (fun z => ∏ i, u i z ^ α i) z₀ := by
    rw [iteratedFDeriv_fun_sum_apply (fun α hα => ((hP α hα).1.fun_mul (hh α)).contDiffAt)]
    exact Finset.sum_congr rfl fun α hα => top_mul (hP α hα).1 (hh α) (hP α hα).2.1
  refine ⟨fun k hk => ?_, h2, fun w => ?_⟩
  · rw [iteratedFDeriv_fun_sum_apply (fun α hα => ((hP α hα).1.fun_mul (hh α)).contDiffAt)]
    exact Finset.sum_eq_zero fun α hα =>
      vanish_mul (hP α hα).1 (hh α) (hP α hα).2.1 (b := 0)
        (fun k hk => absurd hk (Nat.not_lt_zero k)) k (by omega)
  · rw [h2, sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [smul_apply, (hP α hα).2.2 w, smul_eq_mul]
    ring

end JetOfMonomialSum

end GroundTheory.Heights₂.Heights.EffectiveHS
