import ReciprocityTheory.AnalyticForms.LeviForms.RegChartA

namespace ReciprocityTheory.AnForm.P.RegularChartScaling

open MeasureTheory Metric Filter Topology Set
open ReciprocityTheory.AnForm.A

noncomputable section

variable {D : ℕ}

lemma log_term_nonneg {x : ℂ} (hx : ‖x‖ ≤ 2) : 0 ≤ Real.log (4 / ‖x‖ ^ 2) := by
  rcases eq_or_lt_of_le (norm_nonneg x) with h | h
  · rw [← h]; simp
  · apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]; nlinarith

lemma rLoc_ge (S : Finset (Fin D)) (m : Fin D → ℕ) {x : Fin D → ℂ} (hx : ∀ i, ‖x i‖ ≤ 2) :
    Real.exp 1 ≤ rLoc S m x := by
  unfold rLoc
  have : 0 ≤ ∑ i ∈ S, (m i : ℝ) * Real.log (4 / ‖x i‖ ^ 2) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (log_term_nonneg (hx i))
  linarith

lemma rLoc_pos (S : Finset (Fin D)) (m : Fin D → ℕ) {x : Fin D → ℂ} (hx : ∀ i, ‖x i‖ ≤ 2) :
    0 < rLoc S m x := (Real.exp_pos 1).trans_le (rLoc_ge S m hx)

lemma norm_coord_le_of_ball {R : ℝ} (hR : R ≤ 2) {x : Fin D → ℂ} (hx : x ∈ ball (0 : Fin D → ℂ) R)
    (i : Fin D) : ‖x i‖ ≤ 2 :=
  (norm_le_pi_norm x i).trans ((mem_ball_zero_iff.1 hx).le.trans hR)

def mTot (S : Finset (Fin D)) (m : Fin D → ℕ) : ℝ := ∑ i ∈ S, (m i : ℝ)

lemma mTot_nonneg (S : Finset (Fin D)) (m : Fin D → ℕ) : 0 ≤ mTot S m :=
  Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

lemma rLoc_le_far (S : Finset (Fin D)) (m : Fin D → ℕ) {x : Fin D → ℂ} {s : ℝ} (hs : 0 < s)
    (hx : ∀ i, s ≤ ‖x i‖) : rLoc S m x ≤ Real.exp 1 + mTot S m * Real.log (4 / s ^ 2) := by
  unfold rLoc mTot
  rw [Finset.sum_mul]
  have : ∑ i ∈ S, (m i : ℝ) * Real.log (4 / ‖x i‖ ^ 2) ≤ ∑ i ∈ S, (m i : ℝ) * Real.log (4 / s ^ 2) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
      (Real.log_le_log (div_pos (by norm_num) (pow_pos (hs.trans_le (hx i)) 2))
        (div_le_div_of_nonneg_left (by norm_num) (pow_pos hs 2) (pow_le_pow_left₀ hs.le (hx i) 2)))
      (Nat.cast_nonneg _)
  linarith

def pmoff (S : Finset (Fin D)) (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (t : ℝ) : ℝ :=
  sSup (φ '' (closedBall z t \ coordDiv S))

section Osc

variable {S : Finset (Fin D)} {u : (Fin D → ℂ) → ℝ} {R C₅ : ℝ}

lemma pmo_bdd (hub : ∀ x ∈ ball (0 : Fin D → ℂ) R \ coordDiv S, u x ≤ C₅) {z : Fin D → ℂ} {s : ℝ}
    (hs : closedBall z s ⊆ ball 0 R) : BddAbove (u '' (closedBall z s \ coordDiv S)) :=
  ⟨C₅, by rintro _ ⟨x, hx, rfl⟩; exact hub x ⟨hs hx.1, hx.2⟩⟩

lemma pmo_nonempty (z : Fin D → ℂ) {s : ℝ} (hs : 0 < s) :
    (u '' (closedBall z s \ coordDiv S)).Nonempty := by
  obtain ⟨x, hx, hf, -⟩ := exists_far_point z hs
  exact ⟨u x, x, ⟨hx, not_mem_coordDiv_of hs hf⟩, rfl⟩

lemma le_pmo (hub : ∀ x ∈ ball (0 : Fin D → ℂ) R \ coordDiv S, u x ≤ C₅) {z : Fin D → ℂ} {s : ℝ}
    (hs : closedBall z s ⊆ ball 0 R) {x : Fin D → ℂ} (hx : x ∈ closedBall z s \ coordDiv S) :
    u x ≤ pmoff S u z s :=
  le_csSup (pmo_bdd hub hs) (mem_image_of_mem u hx)

lemma pmo_le (z : Fin D → ℂ) {s c : ℝ} (hs : 0 < s) (h : ∀ x ∈ closedBall z s \ coordDiv S, u x ≤ c) :
    pmoff S u z s ≤ c :=
  csSup_le (pmo_nonempty z hs) (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)

lemma pmo_mono (hub : ∀ x ∈ ball (0 : Fin D → ℂ) R \ coordDiv S, u x ≤ C₅) {z : Fin D → ℂ}
    {s s' : ℝ} (hs : 0 < s) (hss : s ≤ s') (hs' : closedBall z s' ⊆ ball 0 R) :
    pmoff S u z s ≤ pmoff S u z s' :=
  csSup_le_csSup (pmo_bdd hub hs') (pmo_nonempty z hs)
    (image_mono (sdiff_subset_sdiff_left (closedBall_subset_closedBall hss)))

lemma pmo_lower (hR : R ≤ 2) (hC₅ : 0 ≤ C₅) (m : Fin D → ℕ)
    (hb : ∀ z ∈ ball (0 : Fin D → ℂ) R \ coordDiv S, -C₅ * Real.log (rLoc S m z) ≤ u z ∧ u z ≤ C₅)
    {z : Fin D → ℂ} {s : ℝ} (hs : 0 < s) (hsR : closedBall z s ⊆ ball 0 R) :
    -C₅ * Real.log (Real.exp 1 + mTot S m * Real.log (4 / s ^ 2)) ≤ pmoff S u z s := by
  obtain ⟨x, hx, hf, -⟩ := exists_far_point z hs
  have hxA : x ∉ coordDiv S := not_mem_coordDiv_of hs hf
  have hxB : x ∈ ball (0 : Fin D → ℂ) R := hsR hx
  refine le_trans ?_ (le_pmo (fun y hy => (hb y hy).2) hsR ⟨hx, hxA⟩)
  refine le_trans ?_ (hb x ⟨hxB, hxA⟩).1
  have h1 := rLoc_pos S m (norm_coord_le_of_ball hR hxB)
  have h2 := rLoc_le_far S m hs hf
  have : Real.log (rLoc S m x) ≤ Real.log (Real.exp 1 + mTot S m * Real.log (4 / s ^ 2)) :=
    Real.log_le_log h1 h2
  nlinarith

lemma pmo_le_polyMax {w : (Fin D → ℂ) → ℝ} (hw : UpperSemicontinuousOn w (ball 0 R))
    (hwu : ∀ x ∈ ball (0 : Fin D → ℂ) R \ coordDiv S, u x ≤ w x) {z : Fin D → ℂ} {s : ℝ}
    (hs : 0 < s) (hsR : closedBall z s ⊆ ball 0 R) :
    pmoff S u z s ≤ polyMax w z s :=
  pmo_le z hs fun x hx => (hwu x ⟨hsR hx.1, hx.2⟩).trans (le_polyMax hw hsR hx.1)

lemma polyMax_le_pmo (hub : ∀ x ∈ ball (0 : Fin D → ℂ) R \ coordDiv S, u x ≤ C₅)
    {w : (Fin D → ℂ) → ℝ} {κ : ℝ}
    (hW3 : ∀ x ∈ ball (0 : Fin D → ℂ) R, ∀ δ > 0, ∃ y ∈ ball (0 : Fin D → ℂ) R \ coordDiv S,
        dist y x < δ ∧ w x ≤ max (u y) (-κ) + δ)
    {z : Fin D → ℂ} {s s' : ℝ} (hs : 0 ≤ s) (hss : s < s') (hsR : closedBall z s' ⊆ ball 0 R) :
    polyMax w z s ≤ max (pmoff S u z s') (-κ) := by
  refine polyMax_le' hs fun x hx => ?_
  have hxB : x ∈ ball (0 : Fin D → ℂ) R := hsR (closedBall_subset_closedBall hss.le hx)
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  obtain ⟨y, hy, hyd, hwy⟩ := hW3 x hxB (min δ (s' - s)) (lt_min hδ (by linarith))
  have hyz : y ∈ closedBall z s' := by
    rw [mem_closedBall] at hx ⊢
    have := dist_triangle y x z
    linarith [min_le_right δ (s' - s)]
  have : u y ≤ pmoff S u z s' := le_pmo hub hsR ⟨hyz, hy.2⟩
  have : max (u y) (-κ) ≤ max (pmoff S u z s') (-κ) := max_le_max this le_rfl
  linarith [min_le_left δ (s' - s)]

end Osc

end

end ReciprocityTheory.AnForm.P.RegularChartScaling
