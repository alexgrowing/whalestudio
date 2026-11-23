import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.RegGlue
import ReciprocityTheory.AnalyticForms.LeviForms.RegChartC
import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PMollifierLowerBound

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

noncomputable section

lemma mollifier_bdd {D : ℕ} (ρ : ReciprocityTheory.AnForm.A.Mollifier D) : ∃ b : ℝ, ∀ w, ρ.toFun w ≤ b := by
  have hcs : HasCompactSupport ρ.toFun := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Fin D → ℂ) 1) ?_
    exact ρ.support_subset.trans ball_subset_closedBall
  obtain ⟨b, hb⟩ := ρ.contDiff.continuous.bounded_above_of_compact_support hcs
  exact ⟨b, fun w => (le_abs_self _).trans (hb w)⟩

lemma polyMax_le_pmoff_same {D : ℕ} {S : Finset (Fin D)} {u w : (Fin D → ℂ) → ℝ} {R B κ : ℝ}
    (hub : ∀ x ∈ ball (0 : Fin D → ℂ) R \ ReciprocityTheory.AnForm.A.coordDiv S, u x ≤ B)
    (hW1 : ReciprocityTheory.AnForm.A.IsPsh (ball 0 R) w)
    (hW3 : ∀ x ∈ ball (0 : Fin D → ℂ) R, ∀ δ > 0,
      ∃ y ∈ ball (0 : Fin D → ℂ) R \ ReciprocityTheory.AnForm.A.coordDiv S,
        dist y x < δ ∧ w x ≤ max (u y) (-κ) + δ)
    {z : Fin D → ℂ} {s R' : ℝ} (hs : 0 < s) (hsR : s < R') (hR' : closedBall z R' ⊆ ball 0 R) :
    ReciprocityTheory.AnForm.A.polyMax w z s ≤ max (RegularChartScaling.pmoff S u z s) (-κ) := by
  have hR'0 : 0 < R' := hs.trans hsR
  have hconv := (ReciprocityTheory.AnForm.A.polyMaxLogConvex_thm D (ball 0 R) w z R' isOpen_ball hW1 hR'0 hR').1
  set g : ℝ → ℝ := fun σ => ReciprocityTheory.AnForm.A.polyMax w z (Real.exp σ) with hg
  have hconv' : ConvexOn ℝ (Set.Iio (Real.log R')) g :=
    hconv.subset Set.Iio_subset_Iic_self (convex_Iio _)
  have hcont : ContinuousOn g (Set.Iio (Real.log R')) := hconv'.continuousOn isOpen_Iio
  have hlog : Real.log s < Real.log R' := Real.log_lt_log hs hsR
  have hca : ContinuousAt g (Real.log s) := hcont.continuousAt (Iio_mem_nhds hlog)
  have hsub : closedBall z s ⊆ ball 0 R := (closedBall_subset_closedBall hsR.le).trans hR'
  have hle : ∀ σ ∈ Set.Iio (Real.log s), g σ ≤ max (RegularChartScaling.pmoff S u z s) (-κ) := by
    intro σ hσ
    have hlt : Real.exp σ < s := by
      have := Real.exp_lt_exp.2 (Set.mem_Iio.1 hσ)
      rwa [Real.exp_log hs] at this
    exact RegularChartScaling.polyMax_le_pmo hub hW3 (Real.exp_pos σ).le hlt hsub
  have hfin : g (Real.log s) ≤ max (RegularChartScaling.pmoff S u z s) (-κ) :=
    le_of_tendsto (hca.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio (Real.log s))))
      (by filter_upwards [self_mem_nhdsWithin] with σ hσ using hle σ hσ)
  simpa only [hg, Real.exp_log hs] using hfin

theorem molli_trunc_near_polyMax :
    ∀ (D : ℕ) (S : Finset (Fin D)) (m : Fin D → ℕ) (u : (Fin D → ℂ) → ℝ) (C₅ : ℝ) (ρ : ReciprocityTheory.AnForm.A.Mollifier D), ContinuousOn u (ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S) → ReciprocityTheory.AnForm.A.IsPsh (ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S) u → (∀ z ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S, -C₅ * Real.log (rLoc S m z) ≤ u z ∧ u z ≤ C₅) → ∃ (C t₀ : ℝ) (w : ℝ → (Fin D → ℂ) → ℝ), 1 ≤ C ∧ 0 < t₀ ∧ t₀ ≤ Real.exp (-Real.exp 1) ∧ t₀ ≤ 1 / 8 ∧ ∀ t, 0 < t → t ≤ t₀ → (∀ z ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S, w t z = max (u z) (-C * Real.log (Real.log (1 / t)))) ∧ ContDiffOn ℝ ∞ (ReciprocityTheory.AnForm.A.molli ρ t (w t)) (ball (0 : Fin D → ℂ) (5 / 4)) ∧ ReciprocityTheory.AnForm.A.IsLeviPsh (ball (0 : Fin D → ℂ) (5 / 4)) (ReciprocityTheory.AnForm.A.molli ρ t (w t)) ∧ (∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4) \ ReciprocityTheory.AnForm.A.coordDiv S, u z ≤ ReciprocityTheory.AnForm.A.molli ρ t (w t) z) ∧ ∀ z ∈ ball (0 : Fin D → ℂ) (5 / 4), -C * Real.log (Real.log (1 / t)) ≤ polyMaxOff S u z t ∧ polyMaxOff S u z t - epsT C t ≤ ReciprocityTheory.AnForm.A.molli ρ t (w t) z ∧ ReciprocityTheory.AnForm.A.molli ρ t (w t) z ≤ polyMaxOff S u z t := by
  intro D S m u C₅ ρ hc hp hb
  have hC₅ : 0 ≤ C₅ := RegularChartScaling.fifth_volume_constant_nonneg m (by norm_num) (by norm_num) hb
  have hub : ∀ x ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S, u x ≤ C₅ :=
    fun x hx => (hb x hx).2
  obtain ⟨C₀, ℓ₀, hC₀, hosc⟩ := RegularChartScaling.oscGen m (R := 3 / 2) (by norm_num) (by norm_num)
    hc hp hb (C₁ := 2) (by norm_num)
  obtain ⟨b, hbρ⟩ := mollifier_bdd ρ
  have hb0 : 0 ≤ b := (ρ.nonneg 0).trans (hbρ 0)
  set K : ℝ := Real.pi ^ D * (3 / 2 : ℝ) ^ (2 * D) * b with hK
  have hK0 : 0 ≤ K := by positivity
  set C : ℝ := C₀ * (K + 1) with hC
  have hCC₀ : C₀ ≤ C := by rw [hC]; nlinarith
  have hKC : K * C₀ ≤ C := by rw [hC]; nlinarith
  have hC1 : 1 ≤ C := hC₀.trans hCC₀
  refine ⟨C, min (min (Real.exp (-ℓ₀)) (Real.exp (-Real.exp 1))) (1 / 8),
    fun t => RegularChartScaling.extT S (3 / 2) u (C * Real.log (Real.log (1 / t))), hC1,
    lt_min (lt_min (Real.exp_pos _) (Real.exp_pos _)) (by norm_num),
    (min_le_left _ _).trans (min_le_right _ _), min_le_right _ _, fun t ht htt => ?_⟩
  beta_reduce
  have ht₁ : t ≤ Real.exp (-ℓ₀) := htt.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hℓ₀ : ℓ₀ ≤ Real.log (1 / t) := by
    have h1 : Real.log t ≤ -ℓ₀ := by
      have := Real.log_le_log ht ht₁
      rwa [Real.log_exp] at this
    rw [one_div, Real.log_inv]; linarith
  obtain ⟨he, hCt, hz⟩ := hosc t ht hℓ₀
  set ℓ := Real.log (1 / t) with hℓ
  have hlℓ : 1 ≤ Real.log ℓ := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) he
  have hℓ0 : 0 < ℓ := (Real.exp_pos 1).trans_le he
  set κ : ℝ := C * Real.log ℓ with hκ
  obtain ⟨w, hwe, hW1, hW2, hW3⟩ := RegularChartScaling.ext_exists S (R := 3 / 2) (by norm_num) hC₅ hc hp hub κ
  rw [← hwe]
  have hwu : ∀ x ∈ ball (0 : Fin D → ℂ) (3 / 2) \ ReciprocityTheory.AnForm.A.coordDiv S, u x ≤ w x :=
    fun x hx => by rw [hW2 x hx]; exact le_max_left _ _
  have ht2 : 2 * t ≤ 1 / 8 := by linarith
  obtain ⟨-, hsm, hps, hbd⟩ := (ReciprocityTheory.AnForm.A.mollify_thm D ρ _ w isOpen_ball hW1).1 t ht
  have hsh : ball (0 : Fin D → ℂ) (5 / 4) ⊆ ReciprocityTheory.AnForm.A.shrink (ball (0 : Fin D → ℂ) (3 / 2)) t :=
    fun z hz' => RegularChartScaling.closedBall_sub_of hz' (by linarith)
  have hsm' := hsm.mono hsh
  refine ⟨fun z hz' => by rw [neg_mul]; exact hW2 z hz', hsm', ?_, ?_, ?_⟩
  · exact (ReciprocityTheory.AnForm.A.isPsh_iff_isLeviPsh_thm D _ _ isOpen_ball
      (hsm'.of_le (by norm_cast))).1 (RegularChartScaling.isPsh_mono hps hsh)
  · intro z hz'
    have hzB : z ∈ ball (0 : Fin D → ℂ) (3 / 2) :=
      ball_subset_ball (by norm_num) hz'.1
    exact (hwu z ⟨hzB, hz'.2⟩).trans (hbd z (hsh hz'.1)).1
  · intro z hzB
    obtain ⟨h16, hgap⟩ := hz z hzB
    have hsubR : ∀ s, s ≤ 1 / 4 → closedBall z s ⊆ ball 0 (3 / 2) := fun s hs =>
      RegularChartScaling.closedBall_sub_of hzB (by linarith)
    have hs16 : 0 < t / (8 * 2) := by positivity
    have hmono : ∀ s s', 0 < s → s ≤ s' → s' ≤ 1 / 4 →
        RegularChartScaling.pmoff S u z s ≤ RegularChartScaling.pmoff S u z s' := fun s s' h0 h1 h2 =>
      RegularChartScaling.pmo_mono hub h0 h1 (hsubR s' h2)
    have hκ' : -κ ≤ RegularChartScaling.pmoff S u z (t / (8 * 2)) := by
      have : C₀ * Real.log ℓ ≤ κ :=
        mul_le_mul_of_nonneg_right hCC₀ (by linarith)
      linarith
    have hlow : ∀ s, t / (8 * 2) ≤ s → s ≤ 1 / 4 → -κ ≤ RegularChartScaling.pmoff S u z s :=
      fun s h1 h2 => hκ'.trans (hmono _ _ hs16 h1 h2)
    have hPM : ∀ s, t / (8 * 2) ≤ s → s ≤ 1 / 8 →
        ReciprocityTheory.AnForm.A.polyMax w z s ≤ RegularChartScaling.pmoff S u z s := fun s h1 h2 => by
      have := polyMax_le_pmoff_same hub hW1 hW3 (hs16.trans_le h1)
        (by linarith : s < 1 / 4) (hsubR _ le_rfl)
      rwa [max_eq_left (hlow s h1 (by linarith))] at this
    have hMP : ∀ s, 0 < s → s ≤ 1 / 4 →
        RegularChartScaling.pmoff S u z s ≤ ReciprocityTheory.AnForm.A.polyMax w z s := fun s h0 h1 =>
      RegularChartScaling.pmo_le_polyMax hW1.1 hwu h0 (hsubR s h1)
    obtain ⟨-, hmp⟩ := hbd z (hsh hzB)
    have hlb := GroundTheory.Heights₂.Heights.Regular.MollifiedLowerBound.closed D ρ b _ w z t isOpen_ball hW1 ht
      (hsubR _ (by linarith)) hbρ
    have ht16 : t ≤ 1 / 16 := by linarith
    have hA := hPM (2 * t) (by rw [div_le_iff₀ (by norm_num)]; linarith) ht2
    have hB : RegularChartScaling.pmoff S u z (t / (4 * 2)) ≤ ReciprocityTheory.AnForm.A.polyMax w z (t / 4) :=
      (hmono _ _ (by positivity) (by linarith) (by linarith)).trans
        (hMP _ (by positivity) (by linarith))
    have hPA : RegularChartScaling.pmoff S u z t ≤ ReciprocityTheory.AnForm.A.polyMax w z (2 * t) :=
      (hmono _ _ ht (by linarith) (by linarith)).trans (hMP _ (by positivity) (by linarith))
    have hP2 := hMP (2 * t) (by positivity) (by linarith)
    have hq : 0 ≤ Real.log ℓ / ℓ := div_nonneg (by linarith) hℓ0.le
    have heps : K * epsT C₀ t ≤ epsT C t := by
      simp only [epsT, ← hℓ, mul_div_assoc]
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right hKC hq
    have hgap' : ReciprocityTheory.AnForm.A.polyMax w z (2 * t) - ReciprocityTheory.AnForm.A.polyMax w z (t / 4) ≤
        epsT C₀ t := by linarith
    have hKg := mul_le_mul_of_nonneg_left hgap' hK0
    have hup := hPM t (by rw [div_le_iff₀ (by norm_num)]; linarith) (by linarith)
    show -C * Real.log ℓ ≤ RegularChartScaling.pmoff S u z t ∧
      RegularChartScaling.pmoff S u z t - epsT C t ≤ _ ∧ _ ≤ RegularChartScaling.pmoff S u z t
    refine ⟨?_, ?_, hmp.trans hup⟩
    · rw [neg_mul]
      exact hlow t (by rw [div_le_iff₀ (by norm_num)]; linarith) (by linarith)
    · linarith

end

end GlobalTheory.CompanionTheory.Ar.Giv
