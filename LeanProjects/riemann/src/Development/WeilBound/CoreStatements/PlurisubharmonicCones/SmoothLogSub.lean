import Development.WeilBound.CoreStatements.PlurisubharmonicCones.LevelFree
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.LeviShift
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.OneSlot
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArithIntersectionMultilinearAllStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HermitianCombinationSmoothConjStatement

open Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp

noncomputable section

namespace LevelTowerAlt.Comparison₂

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {P B : Ideal (MRing J)} {e : ℕ}

theorem log_sub_lift (R : AnLogRes P B e) {A A' : HermLine J} (h : A.a = A'.a) (x : R.X) {y : R.X} (hy : y ∈ R.U x) :
    Real.log (A.h (R.lift x y)) = Real.log (A'.h (R.lift x y)) +
      (Real.log (A.h (R.lift y y)) - Real.log (A'.h (R.lift y y))) := by
  obtain ⟨c, hc, e⟩ := R.compat y x y ⟨R.mem_U y, hy⟩
  have hz := (R.mem x y hy).1
  have hp : (∏ k, ‖c k‖ ^ A'.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
  rw [e, A.smul c _ hc, A'.smul c _ hc, h, Real.log_mul hp (A.pos _ hz).ne', Real.log_mul hp (A'.pos _ hz).ne']
  ring

theorem smooth_log_sub (R : AnLogRes P B e) {A A' : HermLine J} (h : A.a = A'.a) (hA : IsSmoothHerm A)
    (hA' : IsSmoothHerm A') : R.A.Smooth fun y => Real.log (A.h (R.lift y y)) - Real.log (A'.h (R.lift y y)) := by
  intro j y hy
  have hn := ((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U ((R.A.chart j).symm y))).mem_nhds
    ⟨hy.1, R.mem_U _⟩
  have h1 := (((potOf_isPotential R A hA).1 ((R.A.chart j).symm y) j).sub
    ((potOf_isPotential R A' hA').1 ((R.A.chart j).symm y) j)).contDiffAt hn
  refine (h1.congr_of_eventuallyEq ?_).contDiffWithinAt
  filter_upwards [hn] with z hz
  have := log_sub_lift R h ((R.A.chart j).symm y) hz.2
  show _ - _ = Real.log (A.h (R.lift _ _)) - Real.log (A'.h (R.lift _ _))
  linarith

theorem position_zero {I : Ideal (MRing J) → (n : ℕ) → (Fin n → HermLine J) → ℝ} (hI : IsIntersectionFamily I)
    (R : AnLogRes P B e) {Θ L : LocPot R.X} {s : R.X → R.X → ℂ} {nb : ℕ} {mb : Fin nb → ℕ} {Wb : Fin nb → Set R.X}
    (hP : IsArithVar P (e + 1)) (hΘ : IsPotential R.A Θ) (hΘp : IsPosPot R.A Θ) (hL : IsPotential R.A L)
    (hs : IsSection R.A L s) (hsnc : IsSNC R.A L s mb Wb) (hle : ∀ x, logNormSec L s x ≤ 0)
    (l : Fin e → ℝ → HermLine J) (hl : ∀ j, Tame R Θ L s (l j)) {A₁ A₂ : ℝ → HermLine J} {f g : MRing J}
    {w : ℝ → ((Σ k, J k) → ℂ) → ℝ} {C : ℝ} (hsm : ∀ᶠ t in 𝓝[>] (0 : ℝ), IsSmoothHerm (A₁ t) ∧ IsSmoothHerm (A₂ t))
    (hw : ∀ᶠ t in 𝓝[>] (0 : ℝ), IsLineIso P (A₁ t).a (A₂ t).a f g ∧ IsDefectOn P (mcPts P) f g (A₁ t) (A₂ t) (w t) ∧
      ∀ x ∉ bdry s, |w t (R.lift x x)| ≤ C * Real.log (rW L s x))
    (hw0 : ∀ K' ⊆ (bdry s)ᶜ, IsCompact K' →
      TendstoUniformlyOn (fun t x => w t (R.lift x x)) (fun _ => 0) (𝓝[>] 0) K') :
    Tendsto (fun t => I P (e + 1) (Fin.snoc (fun j => l j t) (A₂ t)) - I P (e + 1) (Fin.snoc (fun j => l j t) (A₁ t)))
      (𝓝[>] 0) (𝓝 0) := by
  choose ref c href hev using hl
  have h := weak_zero R.A Θ L s mb Wb hΘ hΘp hL hs hsnc hle (fun j => potOf R (ref j))
    (fun j => potOf_isPotential R _ (href j)) (fun t j => potOf R (l j t))
    (fun t j y => Real.log ((l j t).h (R.lift y y)) - Real.log ((ref j).h (R.lift y y))) (fun t x => w t (R.lift x x)) c C
    (fun j => (hev j).mono fun t ht => ⟨smooth_log_sub R ht.2.1 ht.1 (href j), potOf_isPotential R _ ht.1, fun _ => rfl,
      fun x y hy => log_sub_lift R ht.2.1 x hy, ht.2.2.1, ht.2.2.2⟩) ?_ hw0
  · refine h.congr' ?_
    filter_upwards [hsm, hw, eventually_all.2 hev] with t h1 h2 h3
    have := one_coord₂ GlobalTheory.T.resolution_statement_holds Link.goodProjExistsStatement_holds hI R (fun j => l j t) (A₁ t) (A₂ t) f g (w t) hP
      (fun j => (h3 j).1) h1.1 h1.2 h2.1 h2.2.1
    linarith
  · filter_upwards [hsm, hw] with t h1 h2
    refine ⟨?_, h2.2.2⟩
    obtain ⟨w', a1, -, a2⟩ := GlobalTheory.T.line_isomorphism_defect_function K J P B e R (A₁ t) (A₂ t) f g hP.2.1 h2.1 h1.1 h1.2
    refine (OneModel.continuous_of_smooth R.A a2).congr fun x => ?_
    have hz := R.mem x x (R.mem_U x)
    obtain ⟨u, v, huv, hu, -⟩ := OneModel.exists_pair_ne h2.1.2 hz
    rw [a1 _ hz u v huv hu, h2.2.1 _ hz u v huv hu]

theorem comb_single {τ : Type} [Fintype τ] [DecidableEq τ] (l : τ → HermLine J) (a : τ) :
    Top.combLine l (Pi.single a 1) = l a := by
  refine OneSlot.hermLine_ext ?_ (funext fun z => ?_)
  · show ∑ j, (Pi.single a 1 : τ → ℤ) j • (l j).a = _
    simp [Pi.single_apply]
  · show ∏ j, (l j).h z ^ (Pi.single a 1 : τ → ℤ) j = _
    rw [Finset.prod_eq_single a]
    · simp
    · intro b _ hb
      simp [hb]
    · simp

theorem ii_comb_snoc {II : IntersectionSystem} (hII : IsFullIntersectionSystem II) (hP : IsArithVar P (e + 1)) {τ : Type}
    [Fintype τ] [DecidableEq τ] (l : τ → HermLine J) (hl : ∀ a, IsSmoothHerm (l a)) (ν : Fin e → τ → ℤ) (a : τ) :
    II K J P (e + 1) (Fin.snoc (fun k => Top.combLine l (ν k)) (l a)) =
      ∑ w : Fin e → τ, (∏ k, (ν k (w k) : ℝ)) * II K J P (e + 1) (Fin.snoc (fun k => l (w k)) (l a)) := by
  have h := GlobalTheory.T.arith_intersection_multilinear_all II hII K J P (e + 1) τ l (Fin.snoc (α := fun _ => τ → ℤ) ν (Pi.single a 1)) hP hl
  have h1 : (fun k => Top.combLine l (Fin.snoc (α := fun _ => τ → ℤ) ν (Pi.single a 1) k)) =
      Fin.snoc (α := fun _ => HermLine J) (fun k => Top.combLine l (ν k)) (l a) := by
    funext k
    refine Fin.lastCases ?_ (fun k => ?_) k
    · simp [comb_single]
    · simp
  rw [← h1, h, ← (Fin.snocEquiv fun _ => τ).sum_comp, Fintype.sum_prod_type, Finset.sum_eq_single a]
  · refine Finset.sum_congr rfl fun w _ => ?_
    congr 1
    · simp [Fin.prod_univ_castSucc, Fin.snocEquiv]
    · congr 1
      funext k
      refine Fin.lastCases ?_ (fun k => ?_) k <;> simp [Fin.snocEquiv]
  · intro b _ hb
    refine Finset.sum_eq_zero fun w _ => ?_
    simp [Fin.prod_univ_castSucc, Fin.snocEquiv, hb]
  · simp

theorem replace_gen {II : IntersectionSystem} (hII : IsFullIntersectionSystem II) {d : ℕ} (hd : d = e + 1)
    (R : AnLogRes P B e) {Θ L : LocPot R.X} {s : R.X → R.X → ℂ} {nb : ℕ} {mb : Fin nb → ℕ} {Wb : Fin nb → Set R.X}
    (hP : IsArithVar P (e + 1)) (hΘ : IsPotential R.A Θ) (hΘp : IsPosPot R.A Θ) (hL : IsPotential R.A L)
    (hs : IsSection R.A L s) (hsnc : IsSNC R.A L s mb Wb) (hle : ∀ x, logNormSec L s x ≤ 0) {σ : Type} [Fintype σ]
    (A : ℝ → σ → HermLine J) (M : ℝ → HermLine J) (m : σ → ℤ) (n : Fin d → σ → ℤ) (q : Fin d → Prop) [DecidablePred q]
    (hq : ∀ k, q k → n k = m) (hA : ∀ i, Tame R Θ L s fun t => A t i) (hM : Tame R Θ L s M) {f g : MRing J}
    {w : ℝ → ((Σ k, J k) → ℂ) → ℝ} {C : ℝ}
    (hw : ∀ᶠ t in 𝓝[>] (0 : ℝ), IsLineIso P (Top.combLine (A t) m).a (M t).a f g ∧
      IsDefectOn P (mcPts P) f g (Top.combLine (A t) m) (M t) (w t) ∧
      ∀ x ∉ bdry s, |w t (R.lift x x)| ≤ C * Real.log (rW L s x))
    (hw0 : ∀ K' ⊆ (bdry s)ᶜ, IsCompact K' →
      TendstoUniformlyOn (fun t x => w t (R.lift x x)) (fun _ => 0) (𝓝[>] 0) K') :
    Tendsto (fun t => II K J P d (fun k => if q k then M t else Top.combLine (A t) (n k)) -
      II K J P d fun k => Top.combLine (A t) (n k)) (𝓝[>] 0) (𝓝 0) := by
  classical
  subst hd
  have hAs : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i, IsSmoothHerm (A t i) := eventually_all.2 fun i => by
    obtain ⟨_, _, -, h⟩ := hA i
    exact h.mono fun t ht => ht.1
  have hMs : ∀ᶠ t in 𝓝[>] (0 : ℝ), IsSmoothHerm (M t) := by
    obtain ⟨_, _, -, h⟩ := hM
    exact h.mono fun t ht => ht.1
  have hc : ∀ t, (∀ i, IsSmoothHerm (A t i)) → ∀ r, IsSmoothHerm (Top.combLine (A t) r) := fun t h r =>
    (GlobalTheory.T.hermitian_combination_smooth_conj K J σ (A t) r).1 h
  let l : ℝ → Option (Option σ) → HermLine J := fun t o => o.elim (Top.combLine (A t) m) fun o' => o'.elim (M t) (A t)
  let ν : (σ → ℤ) → Option (Option σ) → ℤ := fun r o => o.elim 0 fun o' => o'.elim 0 r
  have hν : ∀ t r, Top.combLine (l t) (ν r) = Top.combLine (A t) r := fun t r => by
    refine OneSlot.hermLine_ext ?_ (funext fun z => ?_)
    · show ∑ j, ν r j • (l t j).a = ∑ j, r j • (A t j).a
      simp [Fintype.sum_option, ν, l]
    · show ∏ j, (l t j).h z ^ ν r j = ∏ j, (A t j).h z ^ r j
      simp [Fintype.prod_option, ν, l]
  have hstep : ∀ i : Fin (e + 1), Tendsto (fun t =>
      II K J P (e + 1) (fun j => if j < i then Top.combLine (A t) (n j) else
        if q j then M t else Top.combLine (A t) (n j)) -
      II K J P (e + 1) (fun j => if j ≤ i then Top.combLine (A t) (n j) else
        if q j then M t else Top.combLine (A t) (n j))) (𝓝[>] 0) (𝓝 0) := by
    intro i
    by_cases hi : q i
    swap
    · refine tendsto_const_nhds.congr fun t => (sub_eq_zero.2 (congrArg _ (funext fun j => ?_))).symm
      rcases lt_trichotomy j i with h | rfl | h
      · simp [h, h.le]
      · simp [hi]
      · simp [h.not_gt, h.not_ge]
    let μ : Fin e → Option (Option σ) → ℤ := fun k =>
      if ¬ i.succAbove k < i ∧ q (i.succAbove k) then Pi.single (some none) 1 else ν (n (i.succAbove k))
    have hμ0 : ∀ k, μ k none = 0 := fun k => by
      simp only [μ]
      split_ifs
      · simp
      · rfl
    have hμ : ∀ t k, Top.combLine (l t) (μ k) = if i.succAbove k < i then Top.combLine (A t) (n (i.succAbove k)) else
        if q (i.succAbove k) then M t else Top.combLine (A t) (n (i.succAbove k)) := fun t k => by
      simp only [μ]
      by_cases h1 : i.succAbove k < i
      · simp [h1, hν]
      · by_cases h2 : q (i.succAbove k)
        · simp only [h1, h2, not_false_eq_true, and_self, if_true, if_false]
          exact comb_single _ _
        · simp [h1, h2, hν]
    have hterm : ∀ u : Fin e → Option (Option σ), Tendsto (fun t => (∏ k, (μ k (u k) : ℝ)) *
        (II K J P (e + 1) (Fin.snoc (fun k => l t (u k)) (M t)) -
          II K J P (e + 1) (Fin.snoc (fun k => l t (u k)) (Top.combLine (A t) m)))) (𝓝[>] 0) (𝓝 0) := by
      intro u
      by_cases hu : ∃ k, u k = none
      · obtain ⟨k, hk⟩ := hu
        rw [Finset.prod_eq_zero (Finset.mem_univ k) (by rw [hk, hμ0, Int.cast_zero])]
        simp
      · have h := position_zero (hII.1 K J) R hP hΘ hΘp hL hs hsnc hle (fun k t => l t (u k)) (fun k => by
          rcases hk : u k with _ | _ | a
          · exact absurd ⟨k, hk⟩ hu
          · exact hM
          · exact hA a) ((hAs.and hMs).mono fun t ht => ⟨hc t ht.1 m, ht.2⟩) hw hw0
        simpa using h.const_mul (∏ k, (μ k (u k) : ℝ))
    have hsum := tendsto_finsetSum Finset.univ fun u (_ : u ∈ Finset.univ) => hterm u
    simp only [Finset.sum_const_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [hAs, hMs] with t h1 h2
    have hl : ∀ o, IsSmoothHerm (l t o) := by
      rintro (_ | _ | a)
      exacts [hc t h1 m, h2, h1 a]
    have s₁ := GlobalTheory.T.intersection_family_symmetric K J (II K J) (hII.1 K J) P e (fun j => if j < i then Top.combLine (A t) (n j) else
      if q j then M t else Top.combLine (A t) (n j)) i hP fun j => by
        split_ifs
        exacts [hc t h1 _, h2, hc t h1 _]
    have s₂ := GlobalTheory.T.intersection_family_symmetric K J (II K J) (hII.1 K J) P e (fun j => if j ≤ i then Top.combLine (A t) (n j) else
      if q j then M t else Top.combLine (A t) (n j)) i hP fun j => by
        split_ifs
        exacts [hc t h1 _, h2, hc t h1 _]
    have hiff : ∀ k : Fin e, i.succAbove k ≤ i ↔ i.succAbove k < i := fun k =>
      ⟨fun h => lt_of_le_of_ne h (Fin.succAbove_ne i k), le_of_lt⟩
    simp only [lt_irrefl, le_refl, hi, if_true, if_false, hiff, hq i hi, ← hμ] at s₁ s₂
    rw [s₁, s₂]
    have e₁ := ii_comb_snoc hII hP (l t) hl μ (some none)
    have e₂ := ii_comb_snoc hII hP (l t) hl μ none
    refine Eq.trans ?_ (congrArg₂ (· - ·) e₁ e₂).symm
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun u _ => mul_sub _ _ _
  have hsum := tendsto_finsetSum Finset.univ fun i (_ : i ∈ Finset.univ) => hstep i
  simp only [Finset.sum_const_zero] at hsum
  refine hsum.congr fun t => ?_
  exact (GlobalTheory.T.telescoping_coordinate_difference (HermLine J) (e + 1) (II K J P (e + 1)) _ _).symm

theorem replace : Replace := by
  intro _ II hII K _ J _ P B e a b R Θ L s nb mb Wb σ _ A M m n f g w C hab hP hΘ hΘp hL hs hsnc hle hA hM hw hw0
  have h := replace_gen hII hab R hP hΘ hΘp hL hs hsnc hle A M m (Fin.append (fun _ : Fin a => m) n)
    (fun k => (k : ℕ) < a) (fun k => by
      refine Fin.addCases (fun k _ => ?_) (fun k hk => ?_) k
      · simp
      · simp at hk) hA hM hw hw0
  refine h.congr fun t => ?_
  congr 2
  · funext k
    refine Fin.addCases (fun k => ?_) (fun k => ?_) k <;> simp
  · funext k
    refine Fin.addCases (fun k => ?_) (fun k => ?_) k <;> simp

end LevelTowerAlt.Comparison₂
