import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorNormPullbackComponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagComponentProjectionSmoothStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KaehlerFormLocallyBoundedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalNormGaussianWeightFormStatement

open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open AlgebraicGeometry CategoryTheory MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.L2DbarEstimates GlobalTheory GlobalTheory.ShFam GlobalTheory.ChernReg GlobalTheory.CxPts GlobalTheory.TrueGeo

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CoverCharts

open Metric

theorem exists_pos_le {ι : Type} [Fintype ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) : ∃ δ > 0, ∀ i, δ ≤ f i := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨1, one_pos, fun i => (IsEmpty.false i).elim⟩
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_min f
    exact ⟨f i₀, hf i₀, hi₀⟩

theorem core_est {d m : ℕ} {X : Type} [TopologicalSpace X] (e : OpenPartialHomeomorph X (ReciprocityTheory.L2DbarEstimates.V d))
    (nn : Fin m → X → ℝ) (hn : ∀ i y, 0 ≤ nn i y ∧ nn i y ≤ 1)
    (y₀ : X) (ε A : ℝ) (hA : 0 ≤ A) (g : Fin m → ReciprocityTheory.L2DbarEstimates.V d → ℂ) (F : Fin m → ReciprocityTheory.L2DbarEstimates.V d → ℝ)
    (hloc : ∀ w ∈ ball (e y₀) ε, w ∈ e.target ∧ ∀ i, nn i (e.symm w) ^ 2 = ‖g i w‖ ^ 2 * Real.exp (-F i w) ∧
      |F i w| ≤ A ∧ ∀ w' ∈ ball (e y₀) ε, ‖g i w - g i w'‖ ≤ A * ‖w - w'‖)
    (κ : ℝ) (hκ0 : 0 < κ) (hκρ : κ ≤ ε / 4) (hκc : κ ≤ Real.exp ((Real.exp 1 - A) / 2) / (2 * (A + 1)))
    (y : X) (hy : y ∈ e.source) (hyK : e y ∈ closedBall (e y₀) (ε / 4)) (hpos : ∀ i, 0 < nn i y)
    (w : ReciprocityTheory.L2DbarEstimates.V d)
    (hw : w ∈ ball (e y) (κ * Real.exp (-((Real.exp 1 - Real.log ((∏ i, nn i y) ^ 2)) / 2)))) :
    w ∈ ball (e y₀) ε ∧ (∀ i, 0 < nn i (e.symm w)) ∧
      Real.exp 1 - Real.log ((∏ i, nn i (e.symm w)) ^ 2) ≤
        Real.exp 1 - Real.log ((∏ i, nn i y) ^ 2) + m * (2 * A + Real.log 4) := by
  set R := Real.exp 1 - Real.log ((∏ i, nn i y) ^ 2) with hR
  have hP : 0 < ∏ i, nn i y := Finset.prod_pos fun i _ => hpos i
  have hP1 : ∏ i, nn i y ≤ 1 := Finset.prod_le_one (fun i _ => (hn i y).1) fun i _ => (hn i y).2
  have hP2 : (∏ i, nn i y) ^ 2 ≤ 1 := pow_le_one₀ hP.le hP1
  have hlogP : Real.log ((∏ i, nn i y) ^ 2) ≤ 0 := Real.log_nonpos (by positivity) hP2
  have hRpos : 0 ≤ R := by have := Real.exp_pos 1; linarith
  have hexpR : Real.exp (-(R / 2)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have hε : 0 < ε := by linarith
  have hwy : dist w (e y) < κ * Real.exp (-(R / 2)) := hw
  have hyy₀ : dist (e y) (e y₀) ≤ ε / 4 := hyK
  have hw0 : w ∈ ball (e y₀) ε := by
    have : κ * Real.exp (-(R / 2)) ≤ κ := mul_le_of_le_one_right hκ0.le hexpR
    show dist w (e y₀) < ε
    linarith [dist_triangle w (e y) (e y₀)]
  have hy0 : e y ∈ ball (e y₀) ε := by show dist (e y) (e y₀) < ε; linarith
  obtain ⟨-, hly⟩ := hloc (e y) hy0
  obtain ⟨-, hlw⟩ := hloc w hw0
  rw [e.left_inv hy] at hly
  have hPsq : (∏ i, nn i y) ^ 2 = Real.exp (Real.exp 1 - R) := by
    rw [hR, sub_sub_cancel, Real.exp_log (by positivity)]
  set c₁ := Real.exp ((Real.exp 1 - A) / 2) with hc₁
  have hc₁pos : 0 < c₁ := Real.exp_pos _
  have hAκ : A * κ ≤ c₁ / 2 := by
    have h1 : (A + 1) * κ ≤ c₁ / 2 := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * (A + 1))] at hκc
      nlinarith
    nlinarith
  have key : ∀ i, nn i y ^ 2 * Real.exp (-(2 * A)) / 4 ≤ nn i (e.symm w) ^ 2 := by
    intro i
    obtain ⟨ey, hFy, hLy⟩ := hly i
    obtain ⟨ew, hFw, -⟩ := hlw i
    set G := ‖g i (e y)‖ with hG
    have hFy' := abs_le.1 hFy
    have hFw' := abs_le.1 hFw

    have hG2 : G ^ 2 = nn i y ^ 2 * Real.exp (F i (e y)) := by
      rw [ey, mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

    have hprod : (∏ k, nn k y) ^ 2 ≤ nn i y ^ 2 := by
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), mul_pow]
      have : (∏ k ∈ Finset.univ.erase i, nn k y) ^ 2 ≤ 1 :=
        pow_le_one₀ (Finset.prod_nonneg fun k _ => (hn k y).1)
          (Finset.prod_le_one (fun k _ => (hn k y).1) fun k _ => (hn k y).2)
      exact mul_le_of_le_one_right (sq_nonneg _) this
    have hGlow2 : Real.exp (Real.exp 1 - R - A) ≤ G ^ 2 := by
      rw [hG2, sub_eq_add_neg (Real.exp 1 - R), Real.exp_add]
      have h1 : Real.exp (Real.exp 1 - R) ≤ nn i y ^ 2 := hPsq ▸ hprod
      have h2 : Real.exp (-A) ≤ Real.exp (F i (e y)) := Real.exp_le_exp.2 (by linarith)
      exact mul_le_mul h1 h2 (Real.exp_pos _).le (sq_nonneg _)
    have hE : c₁ * Real.exp (-(R / 2)) ≤ G := by
      have hE2 : (c₁ * Real.exp (-(R / 2))) ^ 2 = Real.exp (Real.exp 1 - R - A) := by
        rw [hc₁, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        push_cast
        ring
      rw [← hE2] at hGlow2
      exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).1 hGlow2
    have hgw : G / 2 ≤ ‖g i w‖ := by
      have h1 := hLy w hw0
      have h2 : ‖g i (e y) - g i w‖ = ‖g i w - g i (e y)‖ := norm_sub_rev _ _
      have h3 : ‖g i w - g i (e y)‖ ≤ A * ‖w - e y‖ := by
        have := (hloc w hw0).2 i
        exact this.2.2 (e y) hy0
      have h4 : ‖w - e y‖ < κ * Real.exp (-(R / 2)) := by rwa [← dist_eq_norm]
      have h5 : A * ‖w - e y‖ ≤ A * (κ * Real.exp (-(R / 2))) := mul_le_mul_of_nonneg_left h4.le hA
      have h6 : A * (κ * Real.exp (-(R / 2))) ≤ c₁ / 2 * Real.exp (-(R / 2)) := by
        rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hAκ (Real.exp_pos _).le
      have h7 : G ≤ ‖g i w‖ + ‖g i w - g i (e y)‖ := by
        have := norm_sub_norm_le (g i (e y)) (g i w)
        rw [h2] at this; linarith
      linarith
    have hG0 : 0 ≤ G := norm_nonneg _
    calc nn i y ^ 2 * Real.exp (-(2 * A)) / 4 = (nn i y ^ 2 * Real.exp (-A)) / 4 * Real.exp (-A) := by
          rw [show -(2 * A) = -A + -A by ring, Real.exp_add]; ring
      _ ≤ (G ^ 2) / 4 * Real.exp (-A) := by
          gcongr
          rw [hG2]
          exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) (sq_nonneg _)
      _ = (G / 2) ^ 2 * Real.exp (-A) := by ring
      _ ≤ ‖g i w‖ ^ 2 * Real.exp (-F i w) := by
          gcongr
          linarith
      _ = nn i (e.symm w) ^ 2 := ew.symm
  have hposw : ∀ i, 0 < nn i (e.symm w) := by
    intro i
    have h1 : 0 < nn i y ^ 2 * Real.exp (-(2 * A)) / 4 := by have := hpos i; positivity
    have h2 := lt_of_lt_of_le h1 (key i)
    exact lt_of_le_of_ne (hn i _).1 (fun h => by rw [← h] at h2; simp at h2)
  refine ⟨hw0, hposw, ?_⟩
  have hsum : ∀ z : X, (∀ i, 0 < nn i z) → Real.log ((∏ i, nn i z) ^ 2) = ∑ i, Real.log (nn i z ^ 2) := by
    intro z hz
    rw [← Finset.prod_pow, Real.log_prod]
    intro i _; exact pow_ne_zero _ (hz i).ne'
  rw [hsum _ hposw, hR, hsum _ hpos]
  have hterm : ∀ i, Real.log (nn i y ^ 2) - (2 * A + Real.log 4) ≤ Real.log (nn i (e.symm w) ^ 2) := by
    intro i
    have h1 : 0 < nn i y ^ 2 * Real.exp (-(2 * A)) / 4 := by have := hpos i; positivity
    have h2 := Real.log_le_log h1 (key i)
    have h3 : nn i y ^ 2 * Real.exp (-(2 * A)) ≠ 0 := by have := hpos i; positivity
    rw [Real.log_div h3 (by norm_num : (4:ℝ) ≠ 0)] at h2
    rw [Real.log_mul (by have := hpos i; positivity) (Real.exp_pos _).ne', Real.log_exp] at h2
    linarith
  have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  linarith

end GlobalTheory.CoverCharts

namespace GlobalTheory.CoverCharts

open Metric in

theorem exists_charts_margin : ∀ (D : D7) (O : Setup D) (x : ToroidalCompactificationData O.s) (P : PolOf x O.Φ), O.CoreWith x P →
    ∀ (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ), ∃ (n : ℕ) (ch : Fin n → AlgChart (O.var c).str σ (O.var c).dim)
      (K : Fin n → Set (V (O.var c).dim)) (κ B : ℝ), 0 < κ ∧ 0 ≤ B ∧
      (∀ j, IsCompact (K j) ∧ K j ⊆ (ch j).e.target) ∧ (∀ y, ∃ j, y ∈ (ch j).e.source ∧ (ch j).e y ∈ K j) ∧
      ∀ j, ∀ y ∈ (ch j).e.source, (ch j).e y ∈ K j → y ∈ offBd O.Φ c σ →
        ∀ w ∈ Metric.ball ((ch j).e y) (κ * Real.exp (-(O.met.r c σ y / 2))), w ∈ (ch j).e.target ∧
          (ch j).e.symm w ∈ offBd O.Φ c σ ∧ O.met.r c σ ((ch j).e.symm w) ≤ O.met.r c σ y + B ∧
          ∀ ξ : V (O.var c).dim, P.om c σ (ch j) ((ch j).e.symm w) ξ.ofLp ≤ B * ‖ξ‖ ^ 2 := by
  intro D O x P hC c σ
  classical
  let nn : Fin x.m → CxPts (O.var c).str σ → ℝ := fun i y => x.nrm (embOf O.κ.e σ) i ((O.Φ.C c).down y)
  have hn : ∀ i y, 0 ≤ nn i y ∧ nn i y ≤ 1 := fun i y => (x.nrm_div (embOf O.κ.e σ) i).1 _
  have hdiv := fun i => GlobalTheory.DivPullback.isDivNorm_flag D _ _ _ _ _ O.s O.Φ c σ _ _
    (GlobalTheory.T.flag_component_projection_smooth D _ _ _ _ _ O.s O.Φ c) (x.nrm_div (embOf O.κ.e σ) i)
  have hK := P.om_kaehler c σ
  have hoff : ∀ y, y ∈ offBd O.Φ c σ ↔ ∀ i, 0 < nn i y := by
    intro y
    refine ⟨fun h i => x.nrm_pos (y := (O.Φ.C c).down y) h i, fun h hl => ?_⟩
    obtain ⟨i, hi⟩ := (x.liesIn_genBd_iff ((O.Φ.C c).down y)).1 hl
    exact (((x.nrm_div (embOf O.κ.e σ) i).pos_iff _).1 (h i)) hi
  have hr : ∀ y, O.met.r c σ y = Real.exp 1 - Real.log ((∏ i, nn i y) ^ 2) := by
    intro y; rw [hC.r_eq]; rfl
  have loc : ∀ y₀ : CxPts (O.var c).str σ, ∃ (ch : AlgChart (O.var c).str σ (O.var c).dim) (ε A : ℝ)
      (g : Fin x.m → ReciprocityTheory.L2DbarEstimates.V (O.var c).dim → ℂ) (F : Fin x.m → ReciprocityTheory.L2DbarEstimates.V (O.var c).dim → ℝ),
      y₀ ∈ ch.e.source ∧ 0 < ε ∧ 0 ≤ A ∧
      (∀ w ∈ ball (ch.e y₀) ε, ∀ ξ : ReciprocityTheory.L2DbarEstimates.V (O.var c).dim,
        P.om c σ ch (ch.e.symm w) ξ.ofLp ≤ A * ‖ξ‖ ^ 2) ∧
      ∀ w ∈ ball (ch.e y₀) ε, w ∈ ch.e.target ∧ ∀ i, nn i (ch.e.symm w) ^ 2 = ‖g i w‖ ^ 2 * Real.exp (-F i w) ∧
        |F i w| ≤ A ∧ ∀ w' ∈ ball (ch.e y₀) ε, ‖g i w - g i w'‖ ≤ A * ‖w - w'‖ := by
    intro y₀
    obtain ⟨ch, hch⟩ := AlgChart.exists_mem_source (D := (O.var c).dim) (σ := σ) y₀
    obtain ⟨ε₀, hε₀, B₀, hB₀⟩ := GlobalTheory.T.kaehler_form_locally_bounded hK ch hch
    have h2 := fun i => GlobalTheory.T.local_norm_gaussian_weight_form (hdiv i) ch hch
    choose ε hε g F A hA hloc using h2
    obtain ⟨δ, hδ, hδle⟩ := exists_pos_le ε hε
    have hAt : ∀ i, A i ≤ max B₀ 0 + ∑ i, A i := fun i =>
      (Finset.single_le_sum (fun i _ => hA i) (Finset.mem_univ i)).trans (le_add_of_nonneg_left (le_max_right _ _))
    refine ⟨ch, min ε₀ δ, max B₀ 0 + ∑ i, A i, g, F, hch, lt_min hε₀ hδ,
      add_nonneg (le_max_right _ _) (Finset.sum_nonneg fun i _ => hA i), ?_, ?_⟩
    · intro w hw ξ
      refine ((hB₀ w (ball_subset_ball (min_le_left _ _) hw)).2 ξ).trans
        (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
      exact (le_max_left _ _).trans (le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hA i))
    · intro w hw
      refine ⟨(hB₀ w (ball_subset_ball (min_le_left _ _) hw)).1, fun i => ?_⟩
      have hsub : ball (ch.e y₀) (min ε₀ δ) ⊆ ball (ch.e y₀) (ε i) :=
        ball_subset_ball ((min_le_right _ _).trans (hδle i))
      obtain ⟨-, e1, e2, e3⟩ := hloc i w (hsub hw)
      exact ⟨e1, e2.trans (hAt i), fun w' hw' =>
        (e3 w' (hsub hw')).trans (mul_le_mul_of_nonneg_right (hAt i) (norm_nonneg _))⟩
  choose CH EPS AA GG FF hsrc hEPS hAA hKB hLOC using loc
  obtain ⟨t, ht⟩ := CompactSpace.elim_nhds_subcover
    (fun y₀ => (CH y₀).e.source ∩ (CH y₀).e ⁻¹' ball ((CH y₀).e y₀) (EPS y₀ / 4)) fun y₀ =>
      Filter.inter_mem ((CH y₀).e.open_source.mem_nhds (hsrc y₀))
        (((CH y₀).e.continuousAt (hsrc y₀)).preimage_mem_nhds
          (ball_mem_nhds _ (by linarith [hEPS y₀])))
  let pt : Fin t.card → CxPts (O.var c).str σ := fun j => (t.equivFin.symm j : CxPts (O.var c).str σ)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hterm : ∀ j, 0 ≤ (x.m : ℝ) * (2 * AA (pt j) + Real.log 4) := fun j =>
    mul_nonneg (Nat.cast_nonneg _) (by linarith [hAA (pt j)])
  obtain ⟨κ, hκ, hκle⟩ := exists_pos_le
    (fun j => min (EPS (pt j) / 4) (Real.exp ((Real.exp 1 - AA (pt j)) / 2) / (2 * (AA (pt j) + 1))))
    fun j => lt_min (by linarith [hEPS (pt j)]) (div_pos (Real.exp_pos _) (by linarith [hAA (pt j)]))
  have hBj : ∀ j, AA (pt j) + x.m * (2 * AA (pt j) + Real.log 4) ≤
      ∑ j, (AA (pt j) + x.m * (2 * AA (pt j) + Real.log 4)) := fun j =>
    Finset.single_le_sum (f := fun j => AA (pt j) + x.m * (2 * AA (pt j) + Real.log 4))
      (fun j _ => add_nonneg (hAA _) (hterm j)) (Finset.mem_univ j)
  refine ⟨t.card, fun j => CH (pt j), fun j => closedBall ((CH (pt j)).e (pt j)) (EPS (pt j) / 4), κ,
    ∑ j, (AA (pt j) + x.m * (2 * AA (pt j) + Real.log 4)), hκ,
    Finset.sum_nonneg fun j _ => add_nonneg (hAA _) (hterm j), fun j => ⟨isCompact_closedBall _ _, fun w hw =>
      (hLOC (pt j) w (closedBall_subset_ball (by linarith [hEPS (pt j)]) hw)).1⟩, fun y => ?_, ?_⟩
  · have hy : y ∈ ⋃ y₀ ∈ t, (CH y₀).e.source ∩ (CH y₀).e ⁻¹' ball ((CH y₀).e y₀) (EPS y₀ / 4) := by
      rw [ht]; trivial
    obtain ⟨y₀, hy₀t, hyU⟩ := Set.mem_iUnion₂.1 hy
    refine ⟨t.equivFin ⟨y₀, hy₀t⟩, ?_⟩
    have hp : pt (t.equivFin ⟨y₀, hy₀t⟩) = y₀ := by simp [pt]
    simp only [hp]
    exact ⟨hyU.1, ball_subset_closedBall hyU.2⟩
  · intro j y hy hyK hoffy w hw
    rw [hr y] at hw
    obtain ⟨hw0, hposw, hrw⟩ := core_est (CH (pt j)).e nn hn (pt j) (EPS (pt j)) (AA (pt j))
      (hAA _) (GG (pt j)) (FF (pt j)) (hLOC (pt j)) κ hκ ((hκle j).trans (min_le_left _ _))
      ((hκle j).trans (min_le_right _ _)) y hy hyK ((hoff y).1 hoffy) w hw
    refine ⟨(hLOC _ w hw0).1, (hoff _).2 hposw, ?_, fun ξ => ?_⟩
    · rw [hr, hr]
      refine hrw.trans ?_
      linarith [hBj j, hAA (pt j)]
    · refine (hKB (pt j) w hw0 ξ).trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
      linarith [hBj j, hterm j]

end GlobalTheory.CoverCharts
