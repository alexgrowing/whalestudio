import Formalism.HermitianCurvature.StatementLE
namespace Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset

theorem t_LemmaEFromSteps : LemmaEFromSteps := by
  intro hConst hRed hGrid hSign hFit hClaimAll hStep hInd hBox hLB hLA hL2 hPair hCoef hLeib hCut
  intro CR Cd CP h1 h2 h3 C₂ hC2 C₆ hC6 S hr hL hI hRoots hI1 hJ hP hSI hFI
  have hK0 : 0 ≤ 2 * Real.exp 1 * √(C7 CR Cd CP) := by positivity
  have hC2' : 64 ≤ C₂ := by linarith
  have hN : (1:ℝ) ≤ S.Ntot := by exact_mod_cast (by omega : 1 ≤ S.Ntot)
  have hr1 : (1:ℝ) ≤ ((S.r:ℝ)+1)^2 := by
    have : (0:ℝ) ≤ S.r := Nat.cast_nonneg _
    nlinarith
  have hc := hConst S.k S.r S.Ntot C₂ C₆ (S.β - S.α) hr (by linarith) hC6 hI
  have hNr : (1:ℝ) ≤ S.Ntot * ((S.r:ℝ)+1)^2 := by nlinarith
  have hL64 : 64 ≤ S.L := by
    rw [hL, mul_assoc]; nlinarith
  have h6 : 6 * (S.Ntot:ℝ) * S.L ≤ S.β - S.α := by rw [hL]; exact hc.2.2
  apply hRed hGrid hSign hFit S (by linarith) h6 hRoots hI1
  apply hBox hLB hLA hL2 hPair hCoef hLeib hCut S (by linarith) hFI hP
  apply hClaimAll hStep hInd S (4 * S.Ntot) CR Cd CP (by linarith) h1 h2 h3 (by linarith) _ hJ hSI
  rw [hL]
  have : 64 * (1 + 2 * Real.exp 1 * √(C7 CR Cd CP)) * (S.Ntot * ((S.r:ℝ)+1)^2) ≤ C₂ * (S.Ntot * ((S.r:ℝ)+1)^2) :=
    mul_le_mul_of_nonneg_right hC2 (by linarith)
  nlinarith [this]

theorem t_ClaimInduction : ClaimInduction := by
  intro S hJ hstep w
  induction w with
  | nil =>
    intro _ _
    refine ⟨hJ, ?_⟩
    simp [Sys.size, plus, Sys.jn]
  | cons Y w ih =>
    intro hOn hlen
    have hlen' : w.length < S.Ntot := by simpa [Nat.succ_le_iff] using hlen
    have hc := ih hOn.2 hlen'.le
    have h := hstep w Y hOn hlen' hc.1
    refine ⟨h.1, ?_⟩
    rw [h.2, hc.2]
    simp [Sys.size, plus]
    ring

theorem t_ClaimAll : ClaimAll := by
  intro hStep hInd S σ CR Cd CP hσ h1 h2 h3 hL hLL hJ hSI
  apply hInd S hJ
  intro w Y hOn hlen hint
  have hY : Y ∈ (S.step w).J := by
    have := hOn.1
    simpa [Step.J, Sys.box, S.step_a, S.step_L] using this
  have h := hStep S.B (S.step w) S.c σ CR Cd CP hσ h1 h2 h3 (by rw [S.step_L]; exact hL)
    (by rw [S.step_L, S.step_r]; exact hLL) (hSI w hOn.2 hlen) hint Y hY
  have e : S.dens (Y :: w) = LE.sq S.B ((S.step w).d Y) ((S.step w).gX Y) := by
    funext ω; exact S.step_new w Y ω
  rw [e]
  refine ⟨h.1, ?_⟩
  rw [h.2, S.step_P]
  rfl

theorem size_ne_zero (S : Sys) (hR : S.RootsOut) (w : List (Bool × ℝ)) (hA : S.admitted w) : S.size w ≠ 0 := by
  unfold Sys.size
  apply List.prod_ne_zero
  intro h0
  rw [List.mem_map] at h0
  obtain ⟨x, hx, hx0⟩ := h0
  have hP : S.P x.2 = 0 := abs_eq_zero.mp hx0
  unfold Sys.P at hP
  rw [Finset.prod_eq_zero_iff] at hP
  obtain ⟨s, _, hs⟩ := hP
  apply hR s
  have : -S.lam s = x.2 := by linarith
  rw [this]
  exact hA.1 x hx

theorem t_EstEJoint : EstEJoint := by
  intro E W _ D S loc hN hRoots hAdm hwt hgram hJ0 hlim
  have hj : ∀ v, (S v).jsq = (S v).jn := by
    intro v
    unfold Sys.jn Sys.jsq
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => (hJ0 v ω).symm)
  simp only [hj]
  intro w hw
  have hwW : w ∈ D.Wall ∧ D.cnt w ≤ D.Ntop := by simpa [TB.Data.Wb] using hw
  have hsz : ∀ v, (S v).size (loc w v) ≠ 0 := fun v => size_ne_zero (S v) (hRoots v) _ (hAdm w hwW.1 v).1
  have hl : Tendsto (fun ε : ℝ => ∏ v, (S v).principalHermitianLattice ε (loc w v)) (𝓝[>] 0)
      (𝓝 (∏ v, ((S v).size (loc w v) * (S v).jn))) :=
    tendsto_finset_prod _ (fun v _ => hlim v _ (hAdm w hwW.1 v).1
      (by rw [hN]; exact (hAdm w hwW.1 v).2.trans hwW.2))
  have h2 := hl.div_const (D.wt w)
  have hval : (∏ v, ((S v).size (loc w v) * (S v).jn)) / D.wt w = ∏ v, (S v).jn := by
    rw [hwt w hwW.1, Finset.prod_mul_distrib]
    have : (∏ v, (S v).size (loc w v)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun v _ => hsz v)
    field_simp
  rw [hval] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [hgram ε hε w hwW.1]

theorem t_Constants : Constants := by
  intro k r N C₂ C₆ I hr hC h6 hI
  have hk : (0:ℝ) ≤ k := Nat.cast_nonneg _
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg _
  have hrN : (r:ℝ) + 1 ≤ N := by exact_mod_cast hr
  have hq : (0:ℝ) ≤ ((r:ℝ)+1)^2 := by positivity
  have hA : (0:ℝ) ≤ (k:ℝ) * N * ((r:ℝ)+1)^2 := by positivity
  have hB : (0:ℝ) ≤ (N:ℝ)^2 * ((r:ℝ)+1)^2 := by positivity
  have hC6 : C₂ ≤ C₆ := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have : (k:ℝ) * (C₂ * N * ((r:ℝ)+1)^2) = C₂ * ((k:ℝ) * N * ((r:ℝ)+1)^2) := by ring
    rw [this]
    nlinarith [mul_nonneg (sub_nonneg.mpr hC6) hA, mul_nonneg (le_trans hC.le hC6) hB]
  · push_cast
    have e : ((k:ℝ) + 2 * r + 1) * (C₂ * N * ((r:ℝ)+1)^2)
        = C₂ * ((k:ℝ) * N * ((r:ℝ)+1)^2) + C₂ * ((2 * (r:ℝ) + 1) * N * ((r:ℝ)+1)^2) := by ring
    rw [e]
    have h2 : (2 * (r:ℝ) + 1) * N * ((r:ℝ)+1)^2 ≤ 2 * ((N:ℝ)^2 * ((r:ℝ)+1)^2) := by
      have : (2 * (r:ℝ) + 1) * N ≤ 2 * (N:ℝ)^2 := by nlinarith
      nlinarith
    have h3 : C₂ * ((2 * (r:ℝ) + 1) * N * ((r:ℝ)+1)^2) ≤ C₂ * (2 * ((N:ℝ)^2 * ((r:ℝ)+1)^2)) :=
      mul_le_mul_of_nonneg_left h2 hC.le
    nlinarith [mul_nonneg (sub_nonneg.mpr hC6) hA, mul_nonneg (sub_nonneg.mpr h6) hB, mul_nonneg hC.le hB]
  · have : 6 * (N:ℝ) * (C₂ * N * ((r:ℝ)+1)^2) = 6 * C₂ * ((N:ℝ)^2 * ((r:ℝ)+1)^2) := by ring
    rw [this]
    nlinarith [mul_nonneg (sub_nonneg.mpr h6) hB, mul_nonneg (le_trans hC.le hC6) hA]

theorem onBoxes_ofFn (S : Sys) : ∀ (N : ℕ) (Y : Fin N → ℝ),
    S.OnBoxes (List.ofFn Y) ↔ ∀ a : Fin N, Y a ∈ S.box (N - 1 - (a : ℕ)) := by
  intro N
  induction N with
  | zero => intro Y; simp [Sys.OnBoxes]
  | succ N ih =>
    intro Y
    rw [List.ofFn_succ]
    show (Y 0 ∈ S.box (List.ofFn fun i => Y i.succ).length ∧ S.OnBoxes (List.ofFn fun i => Y i.succ)) ↔ _
    rw [List.length_ofFn, ih]
    constructor
    · rintro ⟨h0, h1⟩ a
      refine Fin.cases ?_ (fun b => ?_) a
      · simpa using h0
      · have := h1 b
        have e : N + 1 - 1 - ((b.succ : Fin (N+1)) : ℕ) = N - 1 - (b : ℕ) := by
          simp only [Fin.val_succ]; omega
        rw [e]; exact this
    · intro h
      refine ⟨by simpa using h 0, fun b => ?_⟩
      have := h b.succ
      have e : N + 1 - 1 - ((b.succ : Fin (N+1)) : ℕ) = N - 1 - (b : ℕ) := by
        simp only [Fin.val_succ]; omega
      rw [e] at this; exact this

theorem on_iff (S : Sys) (N : ℕ) (Y : Fin N → ℝ) : (S.fam N).On Y ↔ S.OnBoxes (List.ofFn Y) := by
  rw [onBoxes_ofFn]
  unfold Fam.On
  constructor
  · intro h a; have := h a; rw [S.fam_J] at this; exact this
  · intro h a; rw [S.fam_J]; exact h a

theorem t_BoxLimitFromClaim : BoxLimitFromClaim := by
  intro hLB hLA hL2 hPair hCoef hLeib hCut S hL hFI hP hClaim
  have key : ∀ (N : ℕ) (Y : Fin N → ℝ), N ≤ S.Ntot → S.OnBoxes (List.ofFn Y) →
      Tendsto (fun ε : ℝ => S.principalHermitianLattice ε (plus (List.ofFn Y))) (𝓝[>] 0)
        (𝓝 (S.size (plus (List.ofFn Y)) * S.jn)) := by
    intro N Y hN hOn
    have hinf : ∀ a, ((S.fam N).J a).Infinite := by
      intro a; rw [S.fam_J]; exact Set.Icc_infinite (by linarith)
    have hde : ∀ Y' : Fin N → ℝ, LE.sq S.B ((S.fam N).dw Y') ((S.fam N).gw Y' (S.fam N).u) = S.dens (List.ofFn Y') := by
      intro Y'; funext ω; exact (S.fam_dens N Y' ω).symm
    have hcl : ∀ Y', (S.fam N).On Y' →
        Integrable (LE.sq S.B ((S.fam N).dw Y') ((S.fam N).gw Y' (S.fam N).u)) S.B.μ := by
      intro Y' h'
      rw [hde]
      exact (hClaim _ ((on_iff S N Y').mp h') (by rw [List.length_ofFn]; exact hN)).1
    have h := hLB hLA hL2 hPair hCoef hLeib hCut S.B N (S.fam N) S.c hinf (hFI N hN) hcl Y ((on_iff S N Y).mpr hOn)
    rw [hde, (hClaim _ hOn (by rw [List.length_ofFn]; exact hN)).2] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hP N Y hN hOn ε hε).symm
  intro w hOn hlen
  have := key w.length w.get hlen (by rw [List.ofFn_get]; exact hOn)
  rwa [List.ofFn_get] at this

theorem onBoxes_mem (S : Sys) : ∀ w : List ℝ, S.OnBoxes w → ∀ y ∈ w, ∃ a, a < w.length ∧ y ∈ S.box a := by
  intro w
  induction w with
  | nil => intro _ y hy; simp at hy
  | cons Y w ih =>
    intro h y hy
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact ⟨w.length, by simp, h.1⟩
    · obtain ⟨a, ha, hm⟩ := ih h.2 y hy'
      exact ⟨a, by simp; omega, hm⟩

theorem t_BoxesFit : BoxesFit := by
  intro S hL h6
  have hsub : ∀ a, a < S.Ntot → S.box a ⊆ Set.Icc (S.α + (S.β - S.α) / 3) (S.β - (S.β - S.α) / 3) := by
    intro a ha x hx
    have ha' : (a:ℝ) + 1 ≤ S.Ntot := by exact_mod_cast ha
    have ha0 : (0:ℝ) ≤ a := Nat.cast_nonneg _
    obtain ⟨h1, h2⟩ := hx
    constructor
    · nlinarith
    · nlinarith
  have hdist : ∀ a b, a < b → ∀ x ∈ S.box a, ∀ y ∈ S.box b, S.L ≤ y - x := by
    intro a b hab x hx y hy
    have hab' : (a:ℝ) + 1 ≤ b := by exact_mod_cast hab
    obtain ⟨_, h2⟩ := hx
    obtain ⟨h3, _⟩ := hy
    nlinarith
  refine ⟨hsub, hdist, ?_⟩
  intro w
  induction w with
  | nil => intro _ _; exact ⟨by simp [plus], by simp [plus]⟩
  | cons Y w ih =>
    intro hOn hlen
    have hlen' : w.length < S.Ntot := by simpa [Nat.succ_le_iff] using hlen
    have hA := ih hOn.2 hlen'.le
    have hN : (1:ℝ) ≤ S.Ntot := by exact_mod_cast (by omega : 1 ≤ S.Ntot)
    have hI : 0 ≤ S.β - S.α := by nlinarith
    constructor
    · intro x hx
      simp only [plus, List.map_cons, List.mem_cons] at hx
      rcases hx with rfl | hx
      · have := hsub _ hlen' hOn.1
        exact ⟨by linarith [this.1], by linarith [this.2]⟩
      · exact hA.1 x hx
    · simp only [plus, List.map_cons, List.pairwise_cons]
      refine ⟨?_, hA.2⟩
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨a, ha, hm⟩ := onBoxes_mem S w hOn.2 y hy
      have := hdist a w.length ha y hm Y hOn.1
      show 2 < |Y - y|
      rw [abs_of_nonneg (by linarith)]
      linarith

open MvPolynomial in
theorem degreeOf_prod_linear_le (N n : ℕ) (lam : Fin n → ℝ) (c : ℝ) (a : Fin N) :
    (C c * ∏ b : Fin N, ∏ s : Fin n, (X b + C (lam s)) : MvPolynomial (Fin N) ℝ).degreeOf a ≤ n := by
  classical
  refine (degreeOf_mul_le _ _ _).trans ?_
  rw [degreeOf_C, zero_add]
  refine (degreeOf_prod_le _ _ _).trans ?_
  have h1 : ∀ b : Fin N, degreeOf a (∏ s : Fin n, (X b + C (lam s)) : MvPolynomial (Fin N) ℝ) ≤ if a = b then n else 0 := by
    intro b
    refine (degreeOf_prod_le _ _ _).trans ?_
    have h2 : ∀ s : Fin n, degreeOf a (X b + C (lam s) : MvPolynomial (Fin N) ℝ) ≤ if a = b then 1 else 0 := by
      intro s
      refine (degreeOf_add_le _ _ _).trans ?_
      rw [degreeOf_C, degreeOf_X]
      simp
    refine (Finset.sum_le_sum fun s _ => h2 s).trans ?_
    split_ifs <;> simp
  refine (Finset.sum_le_sum fun b _ => h1 b).trans ?_
  simp

theorem size_ofFn (S : Sys) (N : ℕ) (sg : Fin N → Bool) (Y : Fin N → ℝ) :
    S.size (List.ofFn fun a => (sg a, Y a)) = ∏ a, |S.P (Y a)| := by
  unfold Sys.size
  rw [List.map_ofFn, List.prod_ofFn]
  rfl

theorem t_ReduceToBoxes : ReduceToBoxes := by
  classical
  intro hGrid hSign hFit S hL h6 hRoots hI1 hBox w hA hlen
  obtain ⟨sgn, _, hsgn⟩ := hSign _ S.lam S.α S.β hRoots
  obtain ⟨hsub, _, hAdm⟩ := hFit S hL h6
  have key : ∀ (N : ℕ), N ≤ S.Ntot → ∀ (sg : Fin N → Bool) (Y : Fin N → ℝ), S.admitted (List.ofFn fun a => (sg a, Y a)) →
      Tendsto (fun ε : ℝ => S.principalHermitianLattice ε (List.ofFn fun a => (sg a, Y a))) (𝓝[>] 0)
        (𝓝 (S.size (List.ofFn fun a => (sg a, Y a)) * S.jn)) := by
    intro N hN sg Y hAY
    let Q : ℝ → MvPolynomial (Fin N) ℝ := fun ε => if h : 0 < ε then (hI1 ε h N hN).choose else 0
    let Q₀ : MvPolynomial (Fin N) ℝ :=
      MvPolynomial.C (sgn ^ N * S.jn) * ∏ b : Fin N, ∏ s, (MvPolynomial.X b + MvPolynomial.C (S.lam s))
    have hQ : ∀ ε, 0 < ε → ∀ (sg' : Fin N → Bool) (Y' : Fin N → ℝ), S.admitted (List.ofFn fun a => (sg' a, Y' a)) →
        S.principalHermitianLattice ε (List.ofFn fun a => (sg' a, Y' a)) = MvPolynomial.eval Y' (Q ε) := by
      intro ε hε sg' Y' h'
      simp only [Q, dif_pos hε]
      exact (hI1 ε hε N hN).choose_spec.2 sg' Y' h'
    have hQd : ∀ ε a, (Q ε).degreeOf a ≤ S.k + 2 * S.r + 1 := by
      intro ε a
      by_cases hε : 0 < ε
      · simp only [Q, dif_pos hε]; exact (hI1 ε hε N hN).choose_spec.1 a
      · simp [Q, dif_neg hε]
    have hQ0 : ∀ (sg' : Fin N → Bool) (Y' : Fin N → ℝ), S.admitted (List.ofFn fun a => (sg' a, Y' a)) →
        S.size (List.ofFn fun a => (sg' a, Y' a)) * S.jn = MvPolynomial.eval Y' Q₀ := by
      intro sg' Y' h'
      rw [size_ofFn]
      have : ∀ a, |S.P (Y' a)| = sgn * S.P (Y' a) := by
        intro a
        apply hsgn
        exact h'.1 (sg' a, Y' a) (by rw [List.mem_ofFn]; exact ⟨a, rfl⟩)
      rw [Finset.prod_congr rfl (fun a _ => this a), Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
      simp only [Q₀, map_mul, MvPolynomial.eval_C, map_prod, map_add, MvPolynomial.eval_X, Sys.P]
      ring
    let n := S.k + 2 * S.r + 1
    let lo : Fin N → ℝ := fun a => S.α + (S.β - S.α) / 3 + 2 * ((N - 1 - (a : ℕ) : ℕ) : ℝ) * S.L
    let grid : Fin N → Finset ℝ := fun a => (Finset.range (n + 1)).image fun i : ℕ => lo a + S.L * ((i : ℝ) / (n + 1))
    have hcard : ∀ a, (grid a).card = n + 1 := by
      intro a
      rw [Finset.card_image_of_injective, Finset.card_range]
      intro i i' h
      have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
      have hL0 : S.L ≠ 0 := by linarith
      have h1 : S.L * ((i : ℝ) / (n + 1)) = S.L * ((i' : ℝ) / (n + 1)) := by simpa using h
      have h2 := mul_left_cancel₀ hL0 h1
      have h3 : (i : ℝ) = i' := by field_simp at h2; exact h2
      exact_mod_cast h3
    have hgm : ∀ a, ∀ y ∈ grid a, y ∈ S.box (N - 1 - (a : ℕ)) := by
      intro a y hy
      simp only [grid, Finset.mem_image, Finset.mem_range] at hy
      obtain ⟨i, hi, rfl⟩ := hy
      have hi' : (i : ℝ) ≤ n := by exact_mod_cast Nat.lt_succ_iff.mp hi
      have h01 : (i : ℝ) / (n + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith
      have h00 : (0:ℝ) ≤ (i : ℝ) / (n + 1) := by positivity
      constructor
      · show lo a ≤ _
        nlinarith
      · show _ ≤ lo a + S.L
        nlinarith
    have hconv := hGrid N n ℝ (𝓝[>] 0) Q Q₀ grid hQd (fun a => degreeOf_prod_linear_le N _ S.lam _ a) hcard (by
      intro Y' hY'
      have hOn : S.OnBoxes (List.ofFn Y') := (onBoxes_ofFn S N Y').mpr fun a => hgm a _ (hY' a)
      have hlen' : (List.ofFn Y').length ≤ S.Ntot := by rw [List.length_ofFn]; exact hN
      have hb := hBox _ hOn hlen'
      have hAd := hAdm _ hOn hlen'
      have e : plus (List.ofFn Y') = List.ofFn fun a => (true, Y' a) := by
        unfold plus; rw [List.map_ofFn]; rfl
      rw [e] at hb hAd
      rw [hQ0 _ _ hAd] at hb
      refine hb.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hQ ε hε _ _ hAd) Y
    rw [hQ0 _ _ hAY]
    refine hconv.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hQ ε hε _ _ hAY).symm
  have e : (List.ofFn fun a => ((w.get a).1, (w.get a).2)) = w := by
    have : (fun a => ((w.get a).1, (w.get a).2)) = w.get := by funext a; rfl
    rw [this, List.ofFn_get]
  have := key w.length hlen (fun a => (w.get a).1) (fun a => (w.get a).2) (by rw [e]; exact hA)
  rwa [e] at this

theorem t_PRatioMiddle : PRatioMiddle := by
  intro n lam α β L Y s hαβ hR hL hnL hs h1 h2 h3 h4
  have hI : 0 < β - α := by linarith
  rw [Finset.abs_prod, Finset.abs_prod]
  have hx0 : 0 ≤ 3 * L / (β - α) := by positivity
  have hfac : ∀ t, |Y + lam t| ≤ (1 + 3 * L / (β - α)) * |Y + s + lam t| := by
    intro t
    have hdist : (β - α) / 3 ≤ |Y + s + lam t| := by
      by_contra hc
      push_neg at hc
      apply hR t
      rw [abs_lt] at hc
      constructor <;> linarith [hc.1, hc.2]
    have h5 : |Y + lam t| ≤ |Y + s + lam t| + |s| := by
      rcases abs_cases (Y + lam t) with h | h <;> rcases abs_cases (Y + s + lam t) with h' | h' <;>
        rcases abs_cases s with h'' | h'' <;> linarith [h.1, h'.1, h''.1]
    have h3L : L ≤ 3 * L / (β - α) * |Y + s + lam t| := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hI]; nlinarith
    nlinarith
  calc ∏ t, |Y + lam t| ≤ ∏ t, (1 + 3 * L / (β - α)) * |Y + s + lam t| :=
        Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun t _ => hfac t)
    _ = (1 + 3 * L / (β - α)) ^ n * ∏ t, |Y + s + lam t| := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ Real.exp 3 * ∏ t, |Y + s + lam t| := by
        apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg fun _ _ => abs_nonneg _)
        have h6 : 1 + 3 * L / (β - α) ≤ Real.exp (3 * L / (β - α)) := by
          linarith [Real.add_one_le_exp (3 * L / (β - α))]
        calc (1 + 3 * L / (β - α)) ^ n ≤ (Real.exp (3 * L / (β - α))) ^ n :=
              pow_le_pow_left₀ (by positivity) h6 n
          _ = Real.exp (n * (3 * L / (β - α))) := by rw [Real.exp_nat_mul]
          _ ≤ Real.exp 3 := by
              apply Real.exp_le_exp.mpr
              rw [mul_div_assoc', div_le_iff₀ hI]; nlinarith

theorem t_ConstSign : ConstSign := by
  classical
  intro n lam α β hR
  suffices h : ∀ T : Finset (Fin n), ∃ sg : ℝ, (sg = 1 ∨ sg = -1) ∧
      ∀ Y ∈ Set.Icc α β, |∏ s ∈ T, (Y + lam s)| = sg * ∏ s ∈ T, (Y + lam s) from h Finset.univ
  intro T
  induction T using Finset.induction_on with
  | empty => exact ⟨1, Or.inl rfl, fun Y _ => by simp⟩
  | insert s T hs ih =>
    obtain ⟨sg, hsg, h⟩ := ih
    have hcase : (∀ Y ∈ Set.Icc α β, 0 < Y + lam s) ∨ (∀ Y ∈ Set.Icc α β, Y + lam s < 0) := by
      by_cases h1 : -lam s < α
      · left; intro Y hY; linarith [hY.1]
      · by_cases h2 : β < -lam s
        · right; intro Y hY; linarith [hY.2]
        · exact absurd ⟨not_lt.mp h1, not_lt.mp h2⟩ (hR s)
    rcases hcase with hp | hn
    · refine ⟨sg, hsg, fun Y hY => ?_⟩
      rw [Finset.prod_insert hs, abs_mul, h Y hY, abs_of_pos (hp Y hY)]; ring
    · refine ⟨-sg, by rcases hsg with rfl | rfl <;> simp, fun Y hY => ?_⟩
      rw [Finset.prod_insert hs, abs_mul, h Y hY, abs_of_neg (hn Y hY)]; ring

theorem t_PImportsHold : PImportsHold := by
  intro hPR hFit S hL h6 hn hRoots w hlen
  obtain ⟨hsub, _, _⟩ := hFit S hL h6
  have hN : (1:ℝ) ≤ S.Ntot := by exact_mod_cast (by omega : 1 ≤ S.Ntot)
  have hI : S.α < S.β := by nlinarith
  have hJ : (S.step w).J = S.box w.length := by
    simp [Step.J, Sys.box, S.step_a, S.step_L]
  have hPf : (S.step w).P = fun Y => ∏ s, (Y + S.lam s) := by funext Y; exact S.step_P w Y
  have hmid := hsub w.length hlen
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [hPf]
    apply Continuous.continuousOn
    fun_prop
  · intro Y hY h0
    rw [hJ] at hY
    have hm := hmid hY
    rw [S.step_P, Finset.prod_eq_zero_iff] at h0
    obtain ⟨s, _, hs⟩ := h0
    apply hRoots s
    have : -S.lam s = Y := by linarith
    rw [this]
    exact ⟨by linarith [hm.1], by linarith [hm.2]⟩
  · intro Y s hY hYs
    rw [hJ] at hY hYs
    have hm := hmid hY
    have hms := hmid hYs
    rw [S.step_P, S.step_P]
    have hs : |(-s)| ≤ S.L := by
      rw [abs_neg, abs_le]
      constructor <;> linarith [hY.1, hY.2, hYs.1, hYs.2]
    have := hPR _ S.lam S.α S.β S.L (Y + s) (-s) hI
      (fun t ht => hRoots t ⟨ht.1.le, ht.2.le⟩) (by linarith) hn hs hms.1 hms.2
      (by rw [add_neg_cancel_right]; exact hm.1) (by rw [add_neg_cancel_right]; exact hm.2)
    simpa [add_neg_cancel_right] using this

end Formalism.FourierDecayAlt.P.LEx2
