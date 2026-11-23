import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.AnalyticForms.LeviForms.Energy
import ReciprocityTheory.AnalyticForms.LeviForms.TailBoundA
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LoglogQuotNonneg
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FixedMemberBase
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SingularWeightMonotoneRegularizationStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.Rate

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem locPot_eq {P Q : LocPot X} (hU : P.U = Q.U) (hφ : P.φ = Q.φ) : P = Q := by
  cases P
  cases Q
  simp_all

theorem zero_add_zero_add (Θ : LocPot X) :
    LocPot.ofFun (0 : X → ℝ) + LocPot.ofFun (0 : X → ℝ) + Θ = Θ := by
  refine locPot_eq ?_ ?_
  · funext x
    show ((Set.univ : Set X) ∩ Set.univ) ∩ Θ.U x = Θ.U x
    simp
  · funext x y
    show (0 : ℝ) + 0 + Θ.φ x y = Θ.φ x y
    simp

theorem rsmul_one (Θ : LocPot X) : Θ.rsmul 1 = Θ := by
  refine locPot_eq rfl ?_
  funext x y
  show (1 : ℝ) * Θ.φ x y = Θ.φ x y
  simp

theorem continuous_of_smooth (A : FinHolAtlas e X) {f : X → ℝ} (h : A.Smooth f) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨j, hj⟩ := A.cover x
  have h1 : ContinuousOn (f ∘ (A.chart j).symm) (A.chart j).target := by
    have := (h j).continuousOn
    simpa using this
  have h2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ (A.chart j)) x :=
    ContinuousAt.comp (h1.continuousAt ((A.chart j).open_target.mem_nhds ((A.chart j).map_source hj)))
      ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

theorem smooth_zero (A : FinHolAtlas e X) : A.Smooth (0 : X → ℝ) := fun j => contDiffOn_const

theorem isPsh_zero (A : FinHolAtlas e X) : IsPsh A (LocPot.ofFun (0 : X → ℝ) + LocPot.ofFun (0 : X → ℝ)) := by
  intro x j y _ w
  have h : (LocPot.ofFun (0 : X → ℝ) + LocPot.ofFun (0 : X → ℝ)).φ x ∘ (A.chart j).symm =
      ⇑(0 : (Fin e → ℂ) →L[ℝ] ℝ) := by
    funext z
    show (0 : ℝ) + 0 = 0
    simp
  rw [h, levi_clm]

theorem update_add [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (F : Fin e → LocPot X) (k : Fin e)
    (P Q : LocPot X) (hF : ∀ i, IsPotential A (F i)) (hP : IsPotential A P) (hQ : IsPotential A Q)
    (g : X → ℝ) (hg : Continuous g) :
    mInt A (Function.update F k (P + Q)) g =
      mInt A (Function.update F k P) g + mInt A (Function.update F k Q) g := by
  cases e with
  | zero => exact k.elim0
  | succ e => exact mInt_update_add A F k P Q hF hP hQ g hg

theorem abs_mInt_le_of_words [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (P : Fin e → LocPot X)
    (Θ : LocPot X) (hP : ∀ i, IsPotential A (P i)) (hΘ : IsPotential A Θ) (g : X → ℝ)
    (hg : Continuous g) (B : ℝ)
    (hB : ∀ T : Finset (Fin e), |mInt A (fun i => if i ∈ T then P i + Θ else Θ) g| ≤ B) :
    |mInt A P g| ≤ 2 ^ e * B := by
  classical
  have key : ∀ D T : Finset (Fin e),
      |mInt A (fun k => if k ∈ D then P k else if k ∈ T then P k + Θ else Θ) g| ≤ 2 ^ D.card * B := by
    intro D
    induction D using Finset.induction_on with
    | empty => intro T; simpa using hB T
    | insert i D hi ih =>
      intro T
      have hF : ∀ k, IsPotential A
          ((fun k => if k ∈ D then P k else if k ∈ T then P k + Θ else Θ) k) := by
        intro k
        dsimp only
        split_ifs
        · exact hP k
        · exact isPotentialAdd A _ _ (hP k) hΘ
        · exact hΘ
      have e1 : (fun k => if k ∈ insert i D then P k else if k ∈ T then P k + Θ else Θ) =
          Function.update (fun k => if k ∈ D then P k else if k ∈ T then P k + Θ else Θ) i (P i) := by
        funext k
        by_cases hk : k = i
        · subst hk; simp
        · simp [Function.update_of_ne hk, Finset.mem_insert, hk]
      have e2 : (fun k => if k ∈ D then P k else if k ∈ insert i T then P k + Θ else Θ) =
          Function.update (fun k => if k ∈ D then P k else if k ∈ T then P k + Θ else Θ) i (P i + Θ) := by
        funext k
        by_cases hk : k = i
        · subst hk; simp [hi]
        · simp [Function.update_of_ne hk, Finset.mem_insert, hk]
      have e3 : (fun k => if k ∈ D then P k else if k ∈ T.erase i then P k + Θ else Θ) =
          Function.update (fun k => if k ∈ D then P k else if k ∈ T then P k + Θ else Θ) i Θ := by
        funext k
        by_cases hk : k = i
        · subst hk; simp [hi]
        · simp [Function.update_of_ne hk, Finset.mem_erase, hk]
      have hadd := update_add A _ i (P i) Θ hF (hP i) hΘ g hg
      rw [← e1, ← e2, ← e3] at hadd
      have h1 := ih (insert i T)
      have h2 := ih (T.erase i)
      rw [Finset.card_insert_of_notMem hi, pow_succ]
      have hEq : mInt A (fun k => if k ∈ insert i D then P k else if k ∈ T then P k + Θ else Θ) g =
          mInt A (fun k => if k ∈ D then P k else if k ∈ insert i T then P k + Θ else Θ) g -
            mInt A (fun k => if k ∈ D then P k else if k ∈ T.erase i then P k + Θ else Θ) g := by
        linarith
      rw [hEq]
      refine (abs_sub _ _).trans ?_
      linarith
  have := key Finset.univ ∅
  simpa using this

theorem abs_mInt_le_of_lintegral [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (A : FinHolAtlas e X) (F : Fin e → LocPot X) (hp : ∀ i, IsPotential A (F i)) (hpsh : ∀ i, IsPsh A (F i))
    (g : X → ℝ) (hg : Continuous g) (B : ℝ) (hB : 0 ≤ B)
    (h : ∫⁻ y, ENNReal.ofReal |g y| ∂maMeasure A F ≤ ENNReal.ofReal B) : |mInt A F g| ≤ B := by
  obtain ⟨-, hm⟩ := maMeasure_thm A F hp hpsh
  rw [(hm g hg.measurable).2 (mIntegrableCont A F hp g hg)]
  refine (norm_integral_le_lintegral_norm g).trans ?_
  simp only [Real.norm_eq_abs]
  exact ENNReal.toReal_le_of_le_ofReal hB h

end GlobalTheory.CompanionTheory.Ar.PB.Rate

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem signed_rate : ConvergenceRateStatement → ∀ (e : ℕ) (σ : Type) [Fintype σ] (S : AnSys e σ), 0 < S.t₀ →
    ∃ C' t₁ : ℝ, 0 < t₁ ∧ t₁ ≤ S.t₀ ∧ ∀ t t', 0 < t' → t' ≤ t → t ≤ t₁ →
      ∀ (a : σ) (w : Fin e → σ) (c : Fin e → Bool),
        |mInt S.A (fun i => S.potT (w i) (if c i then t else t')) (fun x => S.phT a t x - S.phT a t' x)| ≤
          C' * Real.log (Real.log (1 / t)) ^ 2 / Real.log (1 / t) := by
  intro hR e σ _ S ht₀
  classical
  letI : MeasurableSpace S.X := borel S.X
  haveI : BorelSpace S.X := ⟨rfl⟩
  have hΘ := S.potΘ
  have hΘp := S.posΘ
  have hΘpsh : IsPsh S.A S.Θ := TailBoundAlt.isPsh_of_isPosPot S.A S.Θ hΘp
  obtain ⟨h1, -, h3⟩ := GlobalTheory.T.singular_weight_monotone_regularization e S.X S.A S.Θ S.L S.s S.nb S.m S.W S.potL S.sec S.snc S.norm_le hΘ hΘp
  obtain ⟨C₀, z1, z2, -⟩ := h3 (LocPot.ofFun 0) 0 (isPotential_ofFun S.A 0 (Rate.smooth_zero S.A))
    (Rate.smooth_zero S.A) (Rate.isPsh_zero S.A)
  obtain ⟨ts, hts⟩ : ∃ ts, ts = min S.t₀ (Real.exp (-Real.exp 1)) := ⟨_, rfl⟩
  obtain ⟨C5, hC5⟩ : ∃ C5, C5 = max S.C₅ C₀ := ⟨_, rfl⟩
  obtain ⟨Cs, hCs⟩ : ∃ Cs, Cs = max |S.C| |C₀| := ⟨_, rfl⟩
  have htsp : 0 < ts := hts ▸ lt_min ht₀ (Real.exp_pos _)
  have hts1 : ts ≤ S.t₀ := hts ▸ min_le_left _ _
  have hts2 : ts ≤ Real.exp (-Real.exp 1) := hts ▸ min_le_right _ _
  have hsing : ∀ a, IsSingWeight S.A S.L S.s (S.th a) (S.ph a) C5 := fun a =>
    h1 _ _ _ _ (hC5 ▸ le_max_left _ _) (S.sing a)
  have hzs : IsSingWeight S.A S.L S.s (LocPot.ofFun 0) 0 C5 := h1 _ _ _ _ (hC5 ▸ le_max_right _ _) z1
  have hreg : ∀ a, IsRegFamily S.A S.Θ S.L S.s (S.th a) (S.ph a) (S.phT a) Cs ts := fun a =>
    GlobalTheory.CompanionTheory.Ar.Giv.isRegFamily_mono S.A S.Θ S.L S.s _ _ _ _ _ _ _ hΘ hΘpsh (S.sing a).1 S.norm_le (S.reg a)
      (hCs ▸ le_max_left _ _) htsp hts1 hts2
  have hzr : IsRegFamily S.A S.Θ S.L S.s (LocPot.ofFun 0) 0 (fun _ => 0) Cs ts :=
    GlobalTheory.CompanionTheory.Ar.Giv.isRegFamily_mono S.A S.Θ S.L S.s _ _ _ _ _ _ _ hΘ hΘpsh z1.1 S.norm_le
      (by
        have := z2
        exact this)
      (hCs ▸ le_max_right _ _) htsp
      (hts2.trans le_rfl) hts2
  have hrate : ∀ (p : σ × (Fin e → σ)) (T : Finset (Fin e)), ∃ C' t₁ : ℝ, 0 < t₁ ∧
      ∀ t t', 0 < t' → t' ≤ t → t ≤ t₁ → ∀ c : Fin e → Bool,
        ∫⁻ y, ENNReal.ofReal |S.phT p.1 t y - S.phT p.1 t' y|
            ∂maMeasure S.A (fun i => (if i ∈ T then S.th (p.2 i) else LocPot.ofFun 0) +
              LocPot.ofFun ((fun (i : Fin e) (τ : ℝ) => if i ∈ T then S.phT (p.2 i) τ else 0) i
                (if c i then t else t')) + S.Θ) ≤
          ENNReal.ofReal (C' * Real.log (Real.log (1 / t)) ^ 2 / Real.log (1 / t)) := by
    intro p T
    refine hR S.A S.Θ S.L S.s S.m S.W hΘ hΘp S.potL S.sec S.snc S.norm_le
      (fun i => if i ∈ T then S.th (p.2 i) else LocPot.ofFun 0)
      (fun i => if i ∈ T then S.ph (p.2 i) else 0)
      (fun i τ => if i ∈ T then S.phT (p.2 i) τ else 0)
      (S.th p.1) (S.ph p.1) (S.phT p.1) C5 Cs ts ?_ ?_ (hsing _) (hreg _)
    · intro i
      by_cases hi : i ∈ T
      · simpa only [hi, if_true] using hsing (p.2 i)
      · simpa only [hi, if_false] using hzs
    · intro i
      by_cases hi : i ∈ T
      · simpa only [hi, if_true] using hreg (p.2 i)
      · simpa only [hi, if_false] using hzr
  choose Cf tf htf hbd using hrate
  obtain ⟨a₀, ha₀, hsmall⟩ := GlobalTheory.CompanionTheory.Ar.Giv.epsT_small Cs
  have ev1 : ∀ᶠ u in 𝓝[>] (0 : ℝ), ∀ (p : σ × (Fin e → σ)) (T : Finset (Fin e)), u ≤ tf p T := by
    refine eventually_all.2 fun p => eventually_all.2 fun T => ?_
    filter_upwards [Ioc_mem_nhdsGT (htf p T)] with u hu using hu.2
  obtain ⟨t₁, hu1, hu2⟩ := (ev1.and (Ioc_mem_nhdsGT (lt_min htsp ha₀))).exists
  have ht₁ : 0 < t₁ := hu2.1
  have ht₁s : t₁ ≤ ts := hu2.2.trans (min_le_left _ _)
  have ht₁a : t₁ ≤ a₀ := hu2.2.trans (min_le_right _ _)

  have hpsh : ∀ (th : LocPot S.X) (ph : S.X → ℝ) (phT : ℝ → S.X → ℝ), IsPotential S.A th →
      IsRegFamily S.A S.Θ S.L S.s th ph phT Cs ts → ∀ τ, 0 < τ → τ ≤ t₁ →
        S.A.Smooth (phT τ) ∧ IsPsh S.A (th + LocPot.ofFun (phT τ) + S.Θ) := by
    intro th ph phT hth hF τ hτ hτ₁
    obtain ⟨-, -, H⟩ := hF
    obtain ⟨hsm, -, -, -, hp, -⟩ := H τ hτ (hτ₁.trans ht₁s)
    refine ⟨hsm, ?_⟩
    have hε : epsT Cs τ ≤ 1 := by
      have := (abs_le.1 (hsmall τ hτ (hτ₁.trans ht₁a)).1).2
      linarith
    have := GlobalTheory.CompanionTheory.Ar.Giv.isPsh_rsmul_mono S.A S.Θ th (phT τ) hΘ hΘpsh hth hsm hε hp
    rwa [Rate.rsmul_one] at this
  refine ⟨2 ^ e * ∑ p : σ × (Fin e → σ), ∑ T : Finset (Fin e), |Cf p T|, t₁, ht₁, ht₁s.trans hts1, ?_⟩
  intro t t' ht' htt' ht₁' a w c
  have ht : 0 < t := ht'.trans_le htt'
  have htt₁ : t ≤ t₁ := ht₁'
  obtain ⟨K, hK⟩ : ∃ K, K = ∑ p : σ × (Fin e → σ), ∑ T : Finset (Fin e), |Cf p T| := ⟨_, rfl⟩
  obtain ⟨R, hRdef⟩ : ∃ R, R = Real.log (Real.log (1 / t)) ^ 2 / Real.log (1 / t) := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by
    rw [hRdef]
    refine div_nonneg (sq_nonneg _) (Real.log_nonneg ?_)
    have h1t : t ≤ 1 := by
      have := (htt₁.trans ht₁s).trans hts2
      exact this.trans (Real.exp_le_one_iff.2 (by linarith [Real.exp_pos 1]))
    rw [one_div]
    exact (one_le_inv₀ ht).2 h1t
  have hτ : ∀ i, 0 < (if c i then t else t') ∧ (if c i then t else t') ≤ t₁ := by
    intro i
    by_cases hc : c i
    · simp only [hc, if_true]; exact ⟨ht, htt₁⟩
    · simp only [hc]; exact ⟨ht', htt'.trans htt₁⟩
  have hgs : S.A.Smooth (fun x => S.phT a t x - S.phT a t' x) := by
    intro j
    have h1' := (hpsh _ _ _ (S.sing a).1 (hreg a) t ht htt₁).1 j
    have h2' := (hpsh _ _ _ (S.sing a).1 (hreg a) t' ht' (htt'.trans htt₁)).1 j
    exact h1'.sub h2'
  have hg : Continuous (fun x => S.phT a t x - S.phT a t' x) := Rate.continuous_of_smooth S.A hgs
  have hPpot : ∀ i, IsPotential S.A (S.potT (w i) (if c i then t else t')) := fun i =>
    isPotentialAdd S.A _ _ (S.sing (w i)).1 (isPotential_ofFun S.A _
      (hpsh _ _ _ (S.sing (w i)).1 (hreg (w i)) _ (hτ i).1 (hτ i).2).1)
  have hword := Rate.abs_mInt_le_of_words S.A (fun i => S.potT (w i) (if c i then t else t')) S.Θ hPpot hΘ _ hg
    (K * R) ?_
  · rw [hRdef] at hword
    calc _ ≤ _ := hword
      _ = _ := by rw [hK]; ring
  intro T
  have hF : (fun i => if i ∈ T then S.potT (w i) (if c i then t else t') + S.Θ else S.Θ) =
      (fun i => (if i ∈ T then S.th (w i) else LocPot.ofFun 0) +
        LocPot.ofFun ((fun (i : Fin e) (τ : ℝ) => if i ∈ T then S.phT (w i) τ else 0) i
          (if c i then t else t')) + S.Θ) := by
    funext i
    by_cases hi : i ∈ T
    · simp only [hi, if_true]; rfl
    · simp only [hi, if_false]
      exact (Rate.zero_add_zero_add S.Θ).symm
  rw [hF]
  have hpotF : ∀ i, IsPotential S.A ((if i ∈ T then S.th (w i) else LocPot.ofFun 0) +
        LocPot.ofFun ((fun (i : Fin e) (τ : ℝ) => if i ∈ T then S.phT (w i) τ else 0) i
          (if c i then t else t')) + S.Θ) := by
    intro i
    have := congrFun hF i
    simp only at this
    rw [← this]
    by_cases hi : i ∈ T
    · simp only [hi, if_true]
      exact isPotentialAdd S.A _ _ (hPpot i) hΘ
    · simp only [hi, if_false]
      exact hΘ
  have hpshF : ∀ i, IsPsh S.A ((if i ∈ T then S.th (w i) else LocPot.ofFun 0) +
        LocPot.ofFun ((fun (i : Fin e) (τ : ℝ) => if i ∈ T then S.phT (w i) τ else 0) i
          (if c i then t else t')) + S.Θ) := by
    intro i
    have := congrFun hF i
    simp only at this
    rw [← this]
    by_cases hi : i ∈ T
    · simp only [hi, if_true]
      exact (hpsh _ _ _ (S.sing (w i)).1 (hreg (w i)) _ (hτ i).1 (hτ i).2).2
    · simp only [hi, if_false]
      exact hΘpsh
  have hKR : 0 ≤ K * R := by
    refine mul_nonneg ?_ hR0
    rw [hK]
    exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine Rate.abs_mInt_le_of_lintegral S.A _ hpotF hpshF _ hg _ hKR ?_
  refine (hbd (a, w) T t t' ht' htt' (htt₁.trans (hu1 (a, w) T)) c).trans (ENNReal.ofReal_le_ofReal ?_)
  have hCK : Cf (a, w) T ≤ K := by
    have s1 : |Cf (a, w) T| ≤ ∑ T : Finset (Fin e), |Cf (a, w) T| :=
      Finset.single_le_sum (f := fun T => |Cf (a, w) T|) (fun _ _ => abs_nonneg _) (Finset.mem_univ T)
    have s2 : ∑ T : Finset (Fin e), |Cf (a, w) T| ≤ K := by
      rw [hK]
      exact Finset.single_le_sum (f := fun p : σ × (Fin e → σ) => ∑ T : Finset (Fin e), |Cf p T|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ (a, w))
    exact (le_abs_self _).trans (s1.trans s2)
  have := mul_le_mul_of_nonneg_right hCK hR0
  rw [hRdef] at this ⊢
  simpa only [mul_div_assoc] using this

end GlobalTheory.CompanionTheory.Ar.PB
