import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NegLogCoordLeRadius
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Topology ComplexOrder

theorem UpperTheory.holomorphic_ball_inner_region :
    ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ) (e : ℕ) (B : Set (Fin e → ℂ)) (y : (Fin e → ℂ) → CxPts (genStr s.T.Z) σ), IsOpen B → 0 ∈ B → IsHolTo B (fun z => (y z).1) → ContinuousOn y B → ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ᶠ z in 𝓝 (0 : Fin e → ℂ), Inner (y z) → Metric.ball z (c * Real.exp (-(x.r σ (y z)) / 2)) ⊆ {w | Inner (y w)} := by
  intro D A N j S κ s x σ n B y hB h0 hhol hcont
  choose V t f hyV ht hf heq using fun i => (x.nrm_div σ i).2 (y 0)
  set W : Set (Fin n → ℂ) := {z | z ∈ B ∧ ∀ i, y z ∈ ptsIn (genStr s.T.Z) σ (V i).1} with hWdef
  have hWo : IsOpen W := isOpen_iff_mem_nhds.2 fun z hz => by
    have h1 : ∀ᶠ b in 𝓝 z, ∀ i, b ∈ B ∧ ⊤ ≤ (y b).1 ⁻¹ᵁ (V i).1 :=
      Filter.eventually_all.2 fun i => (hhol (V i).1 (t i)).1.mem_nhds ⟨hz.1, hz.2 i⟩
    filter_upwards [h1, hB.mem_nhds hz.1] with b hb hb'
    exact ⟨hb', fun i => (hb i).2⟩
  set G : (Fin n → ℂ) → ℂ := fun z => ∏ i, ev (genStr s.T.Z) σ (V i).1 (t i) (y z) with hG
  have hGd : DifferentiableOn ℂ G W := by
    have h : ∀ i ∈ (Finset.univ : Finset (Fin x.m)),
        DifferentiableOn ℂ (fun z => ev (genStr s.T.Z) σ (V i).1 (t i) (y z)) W :=
      fun i _ => (hhol (V i).1 (t i)).2.mono fun z (hz : z ∈ W) => ⟨hz.1, hz.2 i⟩
    have hu : ∀ u : Finset (Fin x.m),
        DifferentiableOn ℂ (fun z => ∏ i ∈ u, ev (genStr s.T.Z) σ (V i).1 (t i) (y z)) W := by
      intro u
      induction u using Finset.induction_on with
      | empty => simpa using differentiableOn_const (c := (1 : ℂ))
      | insert i u hi ih =>
        simp only [Finset.prod_insert hi]
        exact (h i (Finset.mem_univ i)).mul ih
    exact hu Finset.univ
  have hz₀ : (0 : Fin n → ℂ) ∈ W := ⟨h0, hyV⟩
  have hinn : ∀ z ∈ W, G z ≠ 0 → Inner (y z) := by
    intro z hz hGz
    by_contra hni
    have hb : LiesIn (y z) (genBd s.T.Z) := not_not.1 hni
    obtain ⟨i, hi⟩ := (x.liesIn_genBd_iff _).1 hb
    exact hGz (Finset.prod_eq_zero (Finset.mem_univ i) ((ev_eq_zero_iff (ht i) (hz.2 i)).2 hi))
  have hAn : AnalyticAt ℂ G 0 := GlobalTheory.SCV.analyticOnNhd_of_differentiableOn hWo hGd 0 hz₀
  obtain ⟨K, u, hu, hLip⟩ := (hAn.contDiffAt (n := 1)).hasStrictFDerivAt'
    (hAn.differentiableAt.hasFDerivAt) one_ne_zero |>.exists_lipschitzOnWith
  obtain ⟨R, hR, hsub⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hu (hWo.mem_nhds hz₀))
  set L : ℝ := K + 1 with hL
  have hL0 : 0 < L := by positivity
  set Q : ℝ := ∏ i, Real.exp (1 - f i (y 0)) with hQ
  have hQ0 : 0 < Q := Finset.prod_pos fun i _ => Real.exp_pos _
  have hsQ : 0 < √Q := Real.sqrt_pos.2 hQ0
  set c : ℝ := min (min 1 (R / 2)) (1 / (L * √Q)) with hc
  have hc0 : 0 < c := lt_min (lt_min one_pos (half_pos hR)) (by positivity)
  have hc1 : c ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hc2 : c ≤ R / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hc3 : c ≤ 1 / (L * √Q) := min_le_right _ _
  refine ⟨c, hc0, hc1, ?_⟩
  have hfy : ∀ᶠ p in 𝓝 (y 0), ∀ i, f i (y 0) - 1 < f i p :=
    Filter.eventually_all.2 fun i => (((hf i).continuousOn (isOpen_ptsIn _)).continuousAt
      ((isOpen_ptsIn _).mem_nhds (hyV i))).eventually (lt_mem_nhds (sub_one_lt _))
  have hfz : ∀ᶠ z in 𝓝 (0 : Fin n → ℂ), ∀ i, f i (y 0) - 1 < f i (y z) :=
    (hcont.continuousAt (hB.mem_nhds h0)).eventually hfy
  filter_upwards [Metric.ball_mem_nhds (0 : Fin n → ℂ) (half_pos hR), hfz] with z hzb hfyy
  intro hin w hw
  have hzR : z ∈ Metric.ball (0 : Fin n → ℂ) R := Metric.ball_subset_ball (by linarith) hzb
  have hpy := (hsub hzR).2.2
  have hP0 : 0 < ∏ i, x.nrm σ i (y z) := Finset.prod_pos fun i _ => x.nrm_pos hin i
  have hPeq : (∏ i, x.nrm σ i (y z)) ^ 2 = ‖G z‖ ^ 2 * ∏ i, Real.exp (-f i (y z)) := by
    rw [hG, ← Finset.prod_pow, Finset.prod_congr rfl fun i _ => heq i (y z) (hpy i), Finset.prod_mul_distrib,
      norm_prod, Finset.prod_pow]
  have hE : ∏ i, Real.exp (-f i (y z)) ≤ Q :=
    Finset.prod_le_prod (fun i _ => (Real.exp_pos _).le) fun i _ => Real.exp_le_exp.2 (by linarith [hfyy i])
  have hPle : ∏ i, x.nrm σ i (y z) ≤ ‖G z‖ * √Q := by
    refine (pow_le_pow_iff_left₀ hP0.le (by positivity) two_ne_zero).1 ?_
    rw [hPeq, mul_pow, Real.sq_sqrt hQ0.le]
    exact mul_le_mul_of_nonneg_left hE (sq_nonneg _)
  have hr : x.r σ (y z) = Real.exp 1 - Real.log ((∏ i, x.nrm σ i (y z)) ^ 2) := rfl
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hr0 : 0 ≤ x.r σ (y z) := le_trans he.le (x.exp_le_r σ (y z))
  have hex1 : Real.exp (-(x.r σ (y z)) / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hexP : Real.exp (-(x.r σ (y z)) / 2) ≤ ∏ i, x.nrm σ i (y z) := by
    rw [← Real.le_log_iff_exp_le hP0, hr, Real.log_pow]
    push_cast
    linarith
  have hex0 : 0 < Real.exp (-(x.r σ (y z)) / 2) := Real.exp_pos _
  rw [Metric.mem_ball] at hw hzb
  have hd1 : dist w z < R / 2 := by nlinarith
  have hwR : w ∈ Metric.ball (0 : Fin n → ℂ) R := by
    rw [Metric.mem_ball]
    linarith [dist_triangle w z 0]
  have hd2 : L * dist w z < ‖G z‖ := by
    calc L * dist w z < L * (c * Real.exp (-(x.r σ (y z)) / 2)) := mul_lt_mul_of_pos_left hw hL0
      _ ≤ L * ((1 / (L * √Q)) * (‖G z‖ * √Q)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hc3 (hexP.trans hPle) hex0.le (by positivity)) hL0.le
      _ = ‖G z‖ := by field_simp
  refine hinn w (hsub hwR).2 fun hw0 => ?_
  have h1 := hLip.dist_le_mul w (hsub hwR).1 z (hsub hzR).1
  rw [hw0, dist_comm, dist_zero_right] at h1
  have h2 : (0 : ℝ) ≤ dist w z := dist_nonneg
  nlinarith
