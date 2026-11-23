import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPolynomialEqZeroOfIsOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapNonnegOfDominant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightsOfParts

open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions Formalism.MainNotions.WeightThresholdDefs Filter Topology Classical
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4 GlobalTheory.Mean4O

namespace GlobalTheory.Mean4O

theorem norm_le_of_supAbs_le {D : D7} (Y : ShimX D.what₂.Tau) (u : Wt Y) (L : ℝ) (h : supAbs Y u ≤ L) : ‖u‖ ≤ L := by
  have h0 : 0 ≤ supAbs Y u := Real.iSup_nonneg fun _ => abs_nonneg _
  have hL : 0 ≤ L := h0.trans h
  refine (pi_norm_le_iff_of_nonneg hL).2 fun τ => (pi_norm_le_iff_of_nonneg hL).2 fun i => ?_
  refine le_trans ?_ h
  exact le_ciSup (f := fun x : Rt D.what₂.Tau Y.N => |u x.1 x.2|) (Set.finite_range _).bddAbove (τ, i)

theorem norm_sh_le {D : D7} {Y : ShimX D.what₂.Tau} (A : SlopeTestRemainingChoices Y) (u : Wt Y) (s : ℝ) (hs : 0 ≤ s) :
    ‖A.sh u s‖ ≤ ‖u‖ + s * ‖A.dir‖ := by
  have : A.sh u s = u - s • A.dir := by ext τ i; simp [SlopeTestRemainingChoices.sh]
  rw [this]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, Real.norm_of_nonneg hs]

theorem abs_le_norm_wt {D : D7} {Y : ShimX D.what₂.Tau} (u : Wt Y) (τ : D.what₂.Tau) (i : Fin Y.N) : |u τ i| ≤ ‖u‖ :=
  (norm_le_pi_norm (u τ) i).trans (norm_le_pi_norm u τ)

theorem polySize_of_tie (D : D7) (Y : ShimX D.what₂.Tau) (T : Real0 Y) (A : SlopeTestRemainingChoices Y) (Φ : ℝ → Fn Y) (hd : TieDeg T)
    (hp : TiePs T A) (hl : LimFam Φ) (hv : VertBd T) : PolySize A Φ := by
  obtain ⟨C, hC⟩ := hv
  let U : Set (Option (D.what₂.Tau × Fin Y.N) → ℝ) :=
    {x | (0 < x none ∧ x none < 1) ∧ (∀ y, |x (some y)| < 1) ∧
      ∀ τ (a b : Fin Y.N), a < b → x (some (τ, b)) < x (some (τ, a))}
  have hU : IsOpen U := by
    have h1 : IsOpen {x : Option (D.what₂.Tau × Fin Y.N) → ℝ | 0 < x none ∧ x none < 1} :=
      (isOpen_lt continuous_const (continuous_apply _)).inter (isOpen_lt (continuous_apply _) continuous_const)
    have h2 : IsOpen {x : Option (D.what₂.Tau × Fin Y.N) → ℝ | ∀ y, |x (some y)| < 1} := by
      rw [Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun y => isOpen_lt (continuous_apply _).abs continuous_const
    have h3 : IsOpen {x : Option (D.what₂.Tau × Fin Y.N) → ℝ |
        ∀ τ (a b : Fin Y.N), a < b → x (some (τ, b)) < x (some (τ, a))} := by
      simp only [Set.ofPred_forall]
      exact isOpen_iInter_of_finite fun τ => isOpen_iInter_of_finite fun a => isOpen_iInter_of_finite fun b =>
        isOpen_iInter_of_finite fun _ => isOpen_lt (continuous_apply _) (continuous_apply _)
    exact h1.inter (h2.inter h3)
  have hne : U.Nonempty := by
    refine ⟨fun o => o.elim (1 / 2) (fun y => 1 / (((y.2 : ℕ) : ℝ) + 2)), ⟨by simp, by simp; norm_num⟩, ?_, ?_⟩
    · intro y
      have : (0 : ℝ) ≤ ((y.2 : ℕ) : ℝ) := Nat.cast_nonneg _
      simp only [Option.elim]
      rw [abs_of_pos (by positivity), div_lt_one (by positivity)]
      linarith
    · intro τ a b hab
      have : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
      simp only [Option.elim]
      exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
  obtain ⟨K, hK0, hK⟩ := GlobalTheory.Mean4.coeff_le_of_eval_le (Option (D.what₂.Tau × Fin Y.N)) (dimY Y + 1) U hU hne
  have hb : ∀ c, ∃ M : ℝ, 0 ≤ M ∧ ∀ m, |(A.Ps 2 c).coeff m| ≤ M := by
    intro c
    refine ⟨∑ m ∈ (A.Ps 2 c).support, |(A.Ps 2 c).coeff m|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun m => ?_⟩
    by_cases hm : m ∈ (A.Ps 2 c).support
    · exact Finset.single_le_sum (f := fun m => |(A.Ps 2 c).coeff m|) (fun _ _ => abs_nonneg _) hm
    · rw [notMem_support_iff.1 hm, abs_zero]
      exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  choose M hM0 hM using hb
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨K * C + (∑ c, M c) / Real.log 2, fun B hB => ⟨fun c => ⟨(hp B hB c).1, fun m => ?_⟩, fun u => ?_⟩⟩
  · have h1 : |(A.Ps B c - A.Ps 2 c).coeff m| ≤ K * (C * Real.log B) := by
      refine hK _ _ ((totalDegree_sub _ _).trans (max_le (hp B hB c).1 (hp 2 le_rfl c).1)) (fun x hx => ?_) m
      obtain ⟨⟨hx0, hx1⟩, hx2, hx3⟩ := hx
      let u : Wt Y := fun τ i => x (some (τ, i))
      have hx : x = fun o => o.elim (x none) (fun y => u y.1 y.2) := by
        funext o; cases o <;> rfl
      have he : eval x (A.Ps B c - A.Ps 2 c) = evS Y (A.Ps B c) u (x none) - evS Y (A.Ps 2 c) u (x none) := by
        rw [map_sub]; unfold evS; rw [← hx]
      rw [he]
      have hdom : Dominant Y u := by
        intro τ a b hab
        rcases hab.eq_or_lt with h | h
        · rw [h]
        · exact (hx3 τ a b h).le
      have hn : ‖u‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 fun τ =>
        (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => (hx2 (τ, i)).le
      refine le_of_tendsto (((hp B hB c).2 u (x none)).sub ((hp 2 le_rfl c).2 u (x none))).abs ?_
      filter_upwards [eventually_ge_atTop (Real.exp 2)] with R hR
      exact hC B hB c u hdom hn _ ⟨hx0.le, hx1.le⟩ R hR
    have h2 : M c ≤ ∑ c, M c := Finset.single_le_sum (fun c _ => hM0 c) (Finset.mem_univ c)
    have h3 : Real.log 2 ≤ Real.log B := Real.log_le_log (by norm_num) hB
    have h4 : ∑ c, M c ≤ (∑ c, M c) / Real.log 2 * Real.log B := by
      have := mul_le_mul_of_nonneg_left h3 (div_nonneg ((hM0 c).trans h2) hl2.le)
      rwa [div_mul_cancel₀ _ hl2.ne'] at this
    rw [coeff_sub] at h1
    have h5 := hM c m
    have h6 := abs_add_le (coeff m (A.Ps B c) - coeff m (A.Ps 2 c)) (coeff m (A.Ps 2 c))
    rw [sub_add_cancel] at h6
    nlinarith
  · have h1 : Tendsto (fun R => ∑ c, T.fR B c u 0 R) atTop (𝓝 (∑ c, evS Y (A.Ps B c) u 0)) :=
      tendsto_finsetSum _ fun c _ => (hp B hB c).2 u 0
    refine tendsto_nhds_unique h1 ((hl B hB _).congr' ?_)
    filter_upwards [eventually_ge_atTop (Real.exp 2)] with R hR
    exact hd B hB R hR u

theorem positive_of_tie (D : D7) (V : DivX D) (P : DIV.Align.PrinLev V) (S : HS D) (κ : V.Lev) (hS : HidaSetting D V S κ)
    (hκ : DIV.Align.LevB P κ) (T : Real0 (V.shv S κ)) (A : SlopeTestRemainingChoices (V.shv S κ)) (h1 : NefHodgeTateLattices V P) (h2 : Conclusion2 V P)
    (hF : ∀ c, (T.F c).FamS) (hM : TieM T A) (hN : NefGlue A) : Positive A := by
  refine GlobalTheory.Mean4.positive_of_nef D V P S κ hS hκ h1 h2 A (fun B u s hB => hN B hB u s) fun Λ => ?_
  choose s₀ hs₀ K hK using fun c => hF c (Λ + ‖A.dir‖)
  obtain ⟨s₁, hs₁, hs1, hle⟩ : ∃ s₁ : ℝ, 0 < s₁ ∧ s₁ ≤ 1 ∧ ∀ c, s₁ ≤ s₀ c := by
    have : ∀ᶠ s in 𝓝[>] (0 : ℝ), 0 < s ∧ s ≤ 1 ∧ ∀ c, s ≤ s₀ c := by
      refine eventually_mem_nhdsWithin.and (Eventually.filter_mono nhdsWithin_le_nhds ?_)
      exact (eventually_le_nhds zero_lt_one).and (eventually_all.2 fun c => eventually_le_nhds (hs₀ c))
    exact this.exists
  refine ⟨s₁, hs₁, fun B hB u s hu hΛ hs hss hdom => ?_⟩
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have hn : ‖A.sh u s‖ ≤ Λ + ‖A.dir‖ := by
    have a1 := norm_sh_le A u s hs'.le
    have a2 := norm_le_of_supAbs_le _ u Λ hΛ
    have a3 := mul_le_of_le_one_left (norm_nonneg A.dir) (hss.trans hs1)
    linarith
  have key := fun c σ => hK c (A.sh u s) hdom hn s hs' (hss.trans (hle c)) σ
  exact ((hM B hB u s hu hs).2 hdom fun c σ => (key c σ).1).2.2 fun c σ => (key c σ).2.1

theorem sh_gaps {D : D7} {Y : ShimX D.what₂.Tau} (A : SlopeTestRemainingChoices Y) (u : Wt Y) (t c₀ : ℝ) (ht : 0 < t) (htc : t ≤ c₀)
    (htd : 4 * t * ‖A.dir‖ ≤ 1) (hg : ∀ τ, t ≤ gap Y u τ) (hc : CptGaps Y c₀ u) :
    Dominant Y (A.sh u (t ^ 2)) ∧ ∀ τ, t / 2 ≤ gap Y (A.sh u (t ^ 2)) τ := by
  have key : ∀ τ (a b : Fin Y.N), t ≤ u τ a - u τ b → t / 2 ≤ A.sh u (t ^ 2) τ a - A.sh u (t ^ 2) τ b := by
    intro τ a b h
    have h1 := (abs_le.1 (abs_le_norm_wt A.dir τ a)).2
    have h2 := (abs_le.1 (abs_le_norm_wt A.dir τ b)).1
    have h3 : t ^ 2 * (A.dir τ a - A.dir τ b) ≤ t ^ 2 * (2 * ‖A.dir‖) :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg t)
    have h4 := mul_le_mul_of_nonneg_left htd ht.le
    simp only [SlopeTestRemainingChoices.sh]
    nlinarith
  refine ⟨fun τ => ?_, fun τ => key τ _ _ (hg τ)⟩
  have step : ∀ a b : Fin Y.N, (b : ℕ) = a + 1 → A.sh u (t ^ 2) τ b ≤ A.sh u (t ^ 2) τ a := by
    intro a b hab
    have : t ≤ u τ a - u τ b := by
      by_cases hj : (b : ℕ) = Y.j
      · have h := hg τ
        unfold gap at h
        have ea : a = ⟨Y.j - 1, by have := Y.j_lt; omega⟩ := Fin.ext (by simp only; omega)
        have eb : b = ⟨Y.j, Y.j_lt⟩ := Fin.ext hj
        rwa [← ea, ← eb] at h
      · exact htc.trans (hc τ a b hab hj)
    have := key τ a b this
    linarith
  have ind : ∀ (k : ℕ) (a b : Fin Y.N), (b : ℕ) = a + k → A.sh u (t ^ 2) τ b ≤ A.sh u (t ^ 2) τ a := by
    intro k
    induction k with
    | zero => intro a b h; rw [Fin.ext (show (b : ℕ) = a from h)]
    | succ k ih =>
      intro a b h
      have hb := b.2
      exact (step ⟨a + k, by omega⟩ b (by simp only; omega)).trans (ih a ⟨a + k, by omega⟩ rfl)
  intro a b hab
  exact ind (b - a) a b (by have : (a : ℕ) ≤ b := hab; omega)

theorem heights_of_tie (D : D7) (Y : ShimX D.what₂.Tau) (A : SlopeTestRemainingChoices Y) (H : Ht Y) (h1 : HtCmp A H) (h2 : HtInt H)
    (h3 : HtBd H) (h4 : HtUp A H) : Heights A := by
  obtain ⟨s₀, hs₀, C₁, h1⟩ := h1
  obtain ⟨C₂, h2⟩ := h2
  obtain ⟨C₃, hC₃, hA, h3⟩ := h3
  choose Z hZ C₄ h4 using h4
  refine GlobalTheory.Mean4.heights_of_parts D Y A (fun y => y ∈ H.int) H.falt H.hA fun c₀ hc₀ => ?_
  have hd := norm_nonneg A.dir
  set S := ∑ c, |C₄ c| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have a1 := le_abs_self C₁
  have a1' := abs_nonneg C₁
  have a2 := le_abs_self C₂
  have a2' := abs_nonneg C₂
  set C := |C₁| + |C₂| + C₃ + 3 * S with hC
  refine ⟨min (min s₀ 1) (min c₀ (1 / (4 * (‖A.dir‖ + 1)))), by positivity, C, by linarith,
    fun B hB u t hu hu1 ht htt hg hc => ?_⟩
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  simp only [le_min_iff] at htt
  obtain ⟨⟨t1, t2⟩, t3, t4⟩ := htt
  rw [le_div_iff₀ (by positivity)] at t4
  have t5 : 4 * (t : ℝ) * ‖A.dir‖ ≤ 1 := by nlinarith
  have t6 : (t : ℝ) ^ 2 ≤ t := by nlinarith
  have t7 : (0 : ℝ) < (t : ℝ) ^ 2 := by positivity
  obtain ⟨hdom, hgap⟩ := sh_gaps A u t c₀ ht' t3 t5 hg hc
  have hun := norm_le_of_supAbs_le Y u 1 hu1
  have hn : ‖A.sh u ((t : ℝ) ^ 2)‖ ≤ 2 := by
    have := norm_sh_le A u _ t7.le
    have := mul_le_mul_of_nonneg_right t6 hd
    nlinarith
  have hcmp := h1 B hB u (t ^ 2) hu hun (by positivity) (by push_cast; linarith) (by push_cast; exact hdom)
  push_cast at hcmp
  have lB : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
  have lBt : 0 ≤ Real.log (B / (t : ℝ) ^ 2) := Real.log_nonneg (by rw [le_div_iff₀ t7]; linarith)
  have b1 : C₁ * Real.log B ≤ C * Real.log B := mul_le_mul_of_nonneg_right (by linarith) lB
  refine ⟨fun y hy => ?_, fun y hy => ⟨by linarith [hA y], ?_⟩, fun c => ⟨Z c, hZ c, fun y hy => ?_⟩⟩
  · have e1 := (hcmp y).2.2 hy
    have e2 := h2 _ hdom hn (t / 2) (by linarith) hgap y hy
    have e3 : 0 ≤ Real.log (2 + max (H.falt y) 0) := Real.log_nonneg (by linarith [le_max_right (H.falt y) 0])
    have e4 : C₂ * Real.log (2 + max (H.falt y) 0) ≤ C * Real.log (2 + max (H.falt y) 0) :=
      mul_le_mul_of_nonneg_right (by linarith) e3
    have e5 := mul_le_mul_of_nonneg_left (hA y) t7.le
    have e6 : (t : ℝ) ^ 2 * C₃ ≤ C₃ := mul_le_of_le_one_left (by linarith) (by linarith)
    linarith
  · have e1 := (hcmp y).1
    have e2 := h3 _ hdom hn y hy
    have e0 := hA y
    have e3 : 0 ≤ Real.log (2 + C₃ + H.hA y) := Real.log_nonneg (by linarith)
    have e4 : Real.log (2 + C₃ + H.hA y) ≤ Real.log (2 + C + H.hA y) := Real.log_le_log (by linarith) (by linarith)
    have e5 : C₃ * Real.log (2 + C₃ + H.hA y) ≤ C * Real.log (2 + C + H.hA y) :=
      mul_le_mul (by linarith) e4 e3 (by linarith)
    have e6 : C₁ * Real.log (B / (t : ℝ) ^ 2) ≤ C * Real.log (B / (t : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) lBt
    linarith
  · have e1 := (hcmp y).2.1
    obtain ⟨e2, e3⟩ := h4 c y hy
    have e0 : 0 ≤ C₄ c := (abs_nonneg _).trans e2
    have e4 := (abs_le.1 (e3 (A.sh u ((t : ℝ) ^ 2)))).2
    have e5 := mul_le_mul_of_nonneg_left hn e0
    have e6 := mul_le_mul_of_nonneg_left (abs_le.1 e2).2 t7.le
    have e7 : (t : ℝ) ^ 2 * C₄ c ≤ C₄ c := mul_le_of_le_one_left e0 (by linarith)
    have e8 : |C₄ c| ≤ S := Finset.single_le_sum (f := fun c => |C₄ c|) (fun _ _ => abs_nonneg _) (Finset.mem_univ c)
    have e9 := le_abs_self (C₄ c)
    linarith

theorem size_positive_heights_of_tie : (∀ (D : D7) (Y : ShimX D.what₂.Tau) (T : Real0 Y) (A : SlopeTestRemainingChoices Y) (Φ : ℝ → Fn Y), TieDeg T → TiePs T A → LimFam Φ → VertBd T → PolySize A Φ) ∧ (∀ (D : D7) (V : DivX D) (P : DIV.Align.PrinLev V) (S : HS D) (κ : V.Lev), HidaSetting D V S κ → DIV.Align.LevB P κ → ∀ (T : Real0 (V.shv S κ)) (A : SlopeTestRemainingChoices (V.shv S κ)), NefHodgeTateLattices V P → Conclusion2 V P → (∀ c, (T.F c).FamS) → TieM T A → NefGlue A → Positive A) ∧ (∀ (D : D7) (Y : ShimX D.what₂.Tau) (A : SlopeTestRemainingChoices Y) (H : Ht Y), HtCmp A H → HtInt H → HtBd H → HtUp A H → Heights A) :=
  ⟨polySize_of_tie, positive_of_tie, heights_of_tie⟩

end GlobalTheory.Mean4O
