import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HorizontalCoordinatePolynomialBoundStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousOnFrameDirectionsInverseStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HorizontalCoordinateLatticeIsometryDetOneStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstantPeriodMarkingUniversalCoverStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodLinearAlgebraHodgeSequenceExactStatement

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology

namespace GlobalTheory.ShFam.Hor

theorem exists_log_lift {n : ℕ} (a : ℕ) (z : Fin n → ℂ) (hz : ‖z‖ < 1 / 2) (h0 : ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) :
    ∃ s ∈ logDom n a, logExp a s = z ∧ (∀ j : Fin n, (j : ℕ) < a → |(s j).im| ≤ Real.pi) ∧
      1 + ‖s‖ ≤ 5 * (1 + |Real.log ‖∏ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < a), z k‖|) := by
  classical
  set s : Fin n → ℂ := fun k => if (k : ℕ) < a then Complex.log (z k) else z k with hs
  have hzk : ∀ k, ‖z k‖ < 1 / 2 := fun k => lt_of_le_of_lt (norm_le_pi_norm z k) hz
  have hpos : ∀ k : Fin n, (k : ℕ) < a → 0 < ‖z k‖ := fun k hk => norm_pos_iff.mpr (h0 k hk)
  have hlogneg : ∀ k : Fin n, (k : ℕ) < a → Real.log ‖z k‖ < 0 := fun k hk =>
    Real.log_neg (hpos k hk) (by linarith [hzk k])
  set ℓ := |Real.log ‖∏ k ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < a), z k‖| with hℓ
  have hℓk : ∀ k : Fin n, (k : ℕ) < a → -Real.log ‖z k‖ ≤ ℓ := by
    intro k hk
    rw [hℓ, norm_prod, Real.log_prod]
    · calc -Real.log ‖z k‖ ≤ ∑ j ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < a), -Real.log ‖z j‖ := by
            apply Finset.single_le_sum (f := fun j => -Real.log ‖z j‖)
            · intro j hj
              have := hlogneg j (Finset.mem_filter.mp hj).2
              linarith
            · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
        _ = -∑ j ∈ Finset.univ.filter (fun k : Fin n => (k : ℕ) < a), Real.log ‖z j‖ := by
            rw [Finset.sum_neg_distrib]
        _ ≤ _ := neg_le_abs _
    · intro j hj
      exact (hpos j (Finset.mem_filter.mp hj).2).ne'
  have hℓ0 : 0 ≤ ℓ := abs_nonneg _
  refine ⟨s, ?_, ?_, ?_, ?_⟩
  · intro k
    by_cases hk : (k : ℕ) < a
    · simp only [hk, if_true, hs]
      rw [Complex.log_re]
      exact hlogneg k hk
    · simp only [hk, if_false, hs]
      linarith [hzk k]
  · funext k
    by_cases hk : (k : ℕ) < a
    · simp only [logExp, hk, if_true, hs]
      exact Complex.exp_log (h0 k hk)
    · simp only [logExp, hk, if_false, hs]
  · intro j hj
    simp only [hj, if_true, hs]
    rw [Complex.log_im]
    exact Complex.abs_arg_le_pi _
  · have hsk : ∀ k, ‖s k‖ ≤ ℓ + 4 := by
      intro k
      by_cases hk : (k : ℕ) < a
      · simp only [hk, if_true, hs]
        have h1 : ‖Complex.log (z k)‖ ≤ |(Complex.log (z k)).re| + |(Complex.log (z k)).im| :=
          Complex.norm_le_abs_re_add_abs_im _
        rw [Complex.log_re, Complex.log_im] at h1
        have h2 : |Real.log ‖z k‖| = -Real.log ‖z k‖ := abs_of_neg (hlogneg k hk)
        have h3 := Complex.abs_arg_le_pi (z k)
        have h4 := hℓk k hk
        linarith [Real.pi_lt_four]
      · simp only [hk, if_false, hs]
        linarith [hzk k]
    have : ‖s‖ ≤ ℓ + 4 := (pi_norm_le_iff_of_nonneg (by linarith)).mpr hsk
    linarith

theorem eventually_entries_le {V m n : Type} [TopologicalSpace V] [Fintype m] [Fintype n] {W : V → Matrix m n ℂ} {b₀ : V}
    (h : ContinuousAt W b₀) : ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ b in 𝓝 b₀, ∀ i j, ‖W b i j‖ ≤ M := by
  classical
  have hij : ∀ i j, ∀ᶠ b in 𝓝 b₀, ‖W b i j‖ < ‖W b₀ i j‖ + 1 := by
    intro i j
    have hc : ContinuousAt (fun b => ‖W b i j‖) b₀ :=
      continuous_norm.continuousAt.comp ((continuous_id.matrix_elem i j).continuousAt.comp h)
    exact hc.eventually_lt continuousAt_const (lt_add_one _)
  refine ⟨∑ i, ∑ j, (‖W b₀ i j‖ + 1), ?_, ?_⟩
  · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
  · have hall : ∀ᶠ b in 𝓝 b₀, ∀ i j, ‖W b i j‖ < ‖W b₀ i j‖ + 1 :=
      Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => hij i j
    filter_upwards [hall] with b hb i j
    calc ‖W b i j‖ ≤ ‖W b₀ i j‖ + 1 := (hb i j).le
      _ ≤ ∑ j', (‖W b₀ i j'‖ + 1) :=
          Finset.single_le_sum (f := fun j' => ‖W b₀ i j'‖ + 1) (fun _ _ => by positivity) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', (‖W b₀ i' j'‖ + 1) :=
          Finset.single_le_sum (f := fun i' => ∑ j', (‖W b₀ i' j'‖ + 1))
            (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ i)

theorem differentiableOn_finset_prod {V J : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {u : Finset J} {f : J → V → ℂ}
    {B : Set V} (h : ∀ i ∈ u, DifferentiableOn ℂ (f i) B) : DifferentiableOn ℂ (fun b => ∏ i ∈ u, f i b) B := by
  classical
  induction u using Finset.induction_on with
  | empty => simp [differentiableOn_const]
  | insert i u hi ih =>
    simp only [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i u)).mul (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem logGrowth_of_eq_perVal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (τ : E →+* ℂ) (x : ∀ i, Idx Dw τ → (Fu.Di i).La) (hm : Fin Fu.n → Matrix (Idx Dw τ) (Idx Dw τ) E) (h : CxFr T.Z σ → ℂ), Formalism.L2.PjFree.GoodEmb c σ → 1 ≤ Dw.p + Dw.q → (∀ i, IsPerBasis (Fu.Di i) (x i) (hm i)) → (∀ a i Q, Per Fu a i Q → h a = perVal c σ τ (x i) (hm i) Q) → LogGrowth h := by
  classical
  intro E _ _ _ H Dw l Xo c O _ β Y T σ g e Fu τ x hm h hσ hpq hx hh x₀
  obtain ⟨n, g', r, ka, ch, ex, lam, ρ, hx₀, he0, hL⟩ := GlobalTheory.T.exists_exponential_chart_at_point E H Dw l Xo c O β Y T σ hσ hpq x₀
  obtain ⟨hE, hIn, -, hlam, C0, k0, hC0⟩ := id hL
  refine ⟨ch.source ∩ ch ⁻¹' Metric.ball 0 (1 / 2),
    fun y => ∏ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < ka), ch y j, ?_, ?_, ?_, ?_, ?_⟩
  · exact ch.isOpen_inter_preimage Metric.isOpen_ball
  · refine ⟨hx₀, ?_⟩
    simp only [Set.mem_preimage, he0, Metric.mem_ball, dist_self]
    norm_num
  · intro V _ _ _ B y hB hy hmaps
    show DifferentiableOn ℂ (fun b => ∏ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < ka), ch (y b) j) B
    exact differentiableOn_finset_prod (f := fun j b => ch (y b) j)
      fun j _ => hE.2.1 j V B y hB hy fun b hb => (hmaps hb).1
  · intro y hy
    simp only [Finset.prod_ne_zero_iff, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hIn y hy.1).symm
  · intro V _ _ _ B f hB hf hfN b₀ hb₀
    obtain ⟨i, T₀, hT⟩ := GlobalTheory.T.exists_constant_periodMarking_universalCover E H Dw l Xo c O β T.Z σ g e Fu n g' r ka ch ex lam ρ hL
    obtain ⟨C, k, hCk⟩ := GlobalTheory.T.horizontalCoordinate_polynomial_bound E H Dw l c σ (Fu.Di i) τ (x i) (hm i) g' r T₀ ρ (hx i)
    obtain ⟨W, Wi, hW, hWi, hWW⟩ :=
      GlobalTheory.T.exists_continuousOn_frameDirections_inverse E H Dw l Xo c O β T.Z σ n g' ch ex hE V B f hB hf fun b hb => (hfN b hb).1
    obtain ⟨M, hM0, hMe⟩ := eventually_entries_le (hW.continuousAt (hB.mem_nhds hb₀))
    obtain ⟨M', hM'0, hMe'⟩ := eventually_entries_le (hWi.continuousAt (hB.mem_nhds hb₀))
    set K : ℝ := 1 + M + M' + |C0| * 5 ^ k0 with hK
    have hc5 : 0 ≤ |C0| * 5 ^ k0 := by positivity
    refine ⟨max C 0 * K ^ k, k0 * k, ?_⟩
    filter_upwards [hMe, hMe', hB.mem_nhds hb₀] with b hbW hbWi hbB
    intro hin
    obtain ⟨hys, hyb⟩ := hfN b hbB
    have hyb' : ‖ch (f b).1‖ < 1 / 2 := by
      simpa only [Set.mem_preimage, Metric.mem_ball, dist_zero_right] using hyb
    have hnz : ∀ j : Fin n, (j : ℕ) < ka → ch (f b).1 j ≠ 0 := (hIn _ hys).mp hin
    obtain ⟨s, hsD, hsE, hsIm, hsB⟩ := exists_log_lift ka (ch (f b).1) hyb' hnz
    have hsymm : ch.symm (logExp ka s) = (f b).1 := by rw [hsE]; exact ch.left_inv hys
    obtain ⟨Q, gm, hPer, hIso, hQ⟩ := hT s hsD (f b) (W b) hsymm.symm (hWW b hbB).1
    have hGood := GlobalTheory.T.periodLinearAlgebra_hodgeSequence_exact E H Dw l Xo c O β T.Z σ g e Fu τ (f b) i Q (x i) (hm i) hPer (hx i)
    obtain ⟨hGood', hnorm, -⟩ := GlobalTheory.T.horizontalCoordinate_lattice_isometry_det_one E H Dw l c σ (Fu.Di i) τ (x i) (hm i) Q gm (hx i) hGood hIso
    have hhb : h (f b) = perVal c σ τ (x i) (hm i) Q := hh (f b) i Q hPer
    have hlamb : ‖lam s‖ ≤ C0 * (1 + ‖s‖) ^ k0 := hC0 s hsD (by rw [hsE]; exact hyb'.le) hsIm
    set large₂ : ℝ := 1 + |Real.log ‖∏ j ∈ Finset.univ.filter (fun j : Fin n => (j : ℕ) < ka), ch (f b).1 j‖| with hLg
    have hLg1 : 1 ≤ large₂ := le_add_of_nonneg_right (abs_nonneg _)
    have hpowL : 1 ≤ large₂ ^ k0 := one_le_pow₀ hLg1
    set A : ℝ := max 1 (max (max M M') ‖lam s‖) with hA
    have hA1 : 1 ≤ A := le_max_left _ _
    have hKle : K ≤ K * large₂ ^ k0 := le_mul_of_one_le_right (by linarith) hpowL
    have hlam' : ‖lam s‖ ≤ K * large₂ ^ k0 := by
      calc ‖lam s‖ ≤ C0 * (1 + ‖s‖) ^ k0 := hlamb
        _ ≤ |C0| * (1 + ‖s‖) ^ k0 := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
        _ ≤ |C0| * (5 * large₂) ^ k0 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsB k0) (abs_nonneg _)
        _ = (|C0| * 5 ^ k0) * large₂ ^ k0 := by rw [mul_pow]; ring
        _ ≤ K * large₂ ^ k0 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have hAK : A ≤ K * large₂ ^ k0 :=
      max_le (by linarith) (max_le (max_le (by linarith) (by linarith)) hlam')
    have hb := hCk (Q.comp gm.toLinearMap.toAddMonoidHom) (W b) (Wi b) (lam s) A hGood'
      (hWW b hbB).2.1 (hWW b hbB).2.2 (fun v => hQ v) (hlam s hsD).2.2 hA1
      (fun z j => (hbW z j).trans (le_trans (le_trans (le_max_left M M') (le_max_left _ _)) (le_max_right _ _)))
      (fun j z => (hbWi j z).trans (le_trans (le_trans (le_max_right M M') (le_max_left _ _)) (le_max_right _ _)))
      (fun m j => (norm_le_pi_norm (lam s m) j).trans
        ((norm_le_pi_norm (lam s) m).trans (le_trans (le_max_right _ _) (le_max_right _ _))))
    have hAk : A ^ k ≤ K ^ k * large₂ ^ (k0 * k) := by
      calc A ^ k ≤ (K * large₂ ^ k0) ^ k := pow_le_pow_left₀ (by linarith) hAK k
        _ = K ^ k * large₂ ^ (k0 * k) := by rw [mul_pow, ← pow_mul]
    have hCA : C * A ^ k ≤ max C 0 * K ^ k * large₂ ^ (k0 * k) := by
      calc C * A ^ k ≤ max C 0 * A ^ k := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        _ ≤ max C 0 * (K ^ k * large₂ ^ (k0 * k)) := mul_le_mul_of_nonneg_left hAk (le_max_right _ _)
        _ = max C 0 * K ^ k * large₂ ^ (k0 * k) := by ring
    have key1 : ‖h (f b)‖ ≤ max C 0 * K ^ k * large₂ ^ (k0 * k) := by
      rw [hhb, ← hnorm]; exact hb.1.trans hCA
    have key2 : ‖(h (f b))⁻¹‖ ≤ max C 0 * K ^ k * large₂ ^ (k0 * k) := by
      rw [hhb, norm_inv, ← hnorm, ← norm_inv]; exact hb.2.trans hCA
    exact ⟨key1, key2⟩

end GlobalTheory.ShFam.Hor
