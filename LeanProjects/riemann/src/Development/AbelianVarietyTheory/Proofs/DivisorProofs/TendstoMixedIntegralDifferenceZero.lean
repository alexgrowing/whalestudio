import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChgEqChgWith
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibreSizeAndRangeBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothPotentialTruncationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralTailBoundExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralContinuityEstimate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwiceDifferentiableOfPotential
import ReciprocityTheory.AnalyticForms.PotentialTheory.StokesA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GreenCorrectionLogGrowthStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincarePotentialPshLimitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GreenCorrectionConvergesLocallyStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagPoly GlobalTheory.FlagAr Filter Topology
open GlobalTheory.ArDegIndep
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

noncomputable section

namespace GlobalTheory.ArDegIndep.MixLimit

theorem int_tendsto_zero {e : ℕ} (M : Man e) (K : ℝ) (hK : 0 ≤ K)
    (hT : ∀ σ, ∃ C : ℝ, Tail (M.A σ) (M.Z σ) (M.r σ) (M.Om σ) K C)
    (P : ℝ → Fin e → M.Pot) (g : ℝ → M.Fun) (a : ℝ) (ha : 0 ≤ a)
    (hP : ∀ᶠ R in atTop, ∀ i σ, Comb (M.A σ) (M.Z σ) (M.r σ) (M.Om σ) K (P R i σ))
    (hg : ∀ᶠ R in atTop, ∀ σ, Continuous (g R σ))
    (hlog : ∀ᶠ R in atTop, ∀ σ x, x ∉ M.Z σ → |g R σ x| ≤ a * Real.log (M.r σ x))
    (hsmall : ∀ ℓ δ : ℝ, 0 < δ → ∀ᶠ R in atTop, ∀ σ x, x ∉ M.Z σ → M.r σ x ≤ ℓ → |g R σ x| ≤ δ) :
    Tendsto (fun R => M.int (P R) (g R)) atTop (𝓝 0) := by
  choose C hC using hT
  set S : ℝ := M.κ * ∑ σ, (3 * K) ^ e * |C σ| with hS
  have hS0 : 0 ≤ S := mul_nonneg M.κ_pos.le (Finset.sum_nonneg fun σ _ => by positivity)

  have bound : ∀ δ ℓ : ℝ, 0 < δ → Real.exp 1 ≤ ℓ → ∀ᶠ R in atTop,
      |M.int (P R) (g R)| ≤ S * δ + S * (a * (Real.log ℓ ^ (e + 1) / ℓ)) := by
    intro δ ℓ hδ hℓ
    filter_upwards [hP, hg, hlog, hsmall ℓ δ hδ] with R h1 h2 h3 h4
    have hℓ0 : 0 < ℓ := (Real.exp_pos 1).trans_le hℓ
    have hL0 : 0 ≤ Real.log ℓ ^ (e + 1) / ℓ :=
      div_nonneg (pow_nonneg (Real.log_nonneg (by linarith [Real.add_one_le_exp 1])) _) hℓ0.le
    have term : ∀ σ, |mInt (M.A σ) (fun i => P R i σ) (g R σ)| ≤
        (3 * K) ^ e * |C σ| * δ + (3 * K) ^ e * |C σ| * (a * (Real.log ℓ ^ (e + 1) / ℓ)) := by
      intro σ
      refine (GlobalTheory.Mean4O.CombInt.abs_mInt_comb_le e (M.X σ) (M.A σ) (M.Z σ) (M.r σ) (M.Om σ) (M.bd σ) K (C σ) hK
        (hC σ) (fun i => P R i σ) (g R σ) δ a ℓ (fun i => h1 i σ) (h2 σ) hδ.le ha hℓ
        (fun x hx hr => h4 σ x hx hr) (fun x hx _ => h3 σ x hx)).trans ?_
      have e1 : δ * C σ ≤ δ * |C σ| := mul_le_mul_of_nonneg_left (le_abs_self _) hδ.le
      have e2 : a * (C σ * Real.log ℓ ^ (e + 1) / ℓ) ≤ a * (|C σ| * (Real.log ℓ ^ (e + 1) / ℓ)) := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self _) hL0) ha
      have e3 : (0 : ℝ) ≤ (3 * K) ^ e := by positivity
      calc (3 * K) ^ e * (δ * C σ + a * (C σ * Real.log ℓ ^ (e + 1) / ℓ))
          ≤ (3 * K) ^ e * (δ * |C σ| + a * (|C σ| * (Real.log ℓ ^ (e + 1) / ℓ))) :=
            mul_le_mul_of_nonneg_left (add_le_add e1 e2) e3
        _ = _ := by ring
    unfold Man.int
    rw [abs_mul, abs_of_pos M.κ_pos]
    calc M.κ * |∑ σ, mInt (M.A σ) (fun i => P R i σ) (g R σ)|
        ≤ M.κ * ∑ σ, ((3 * K) ^ e * |C σ| * δ + (3 * K) ^ e * |C σ| * (a * (Real.log ℓ ^ (e + 1) / ℓ))) :=
          mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun σ _ => term σ))
            M.κ_pos.le
      _ = _ := by rw [hS, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]; ring
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hL : Tendsto (fun ℓ : ℝ => Real.log ℓ ^ (e + 1) / (1 * ℓ + 0)) atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 (e + 1) one_ne_zero
  have hSa : 0 ≤ S * a := mul_nonneg hS0 ha
  obtain ⟨ℓ, hℓ1, hℓ2⟩ := ((hL.eventually (gt_mem_nhds (show (0 : ℝ) < ε / (2 * (S * a + 1)) by positivity))).and
    (eventually_ge_atTop (Real.exp 1))).exists
  simp only [one_mul, add_zero] at hℓ1
  filter_upwards [bound (ε / (2 * (S + 1))) ℓ (by positivity) hℓ2] with R hR
  rw [Real.dist_eq, sub_zero]
  refine lt_of_le_of_lt hR ?_
  have f1 : S * (ε / (2 * (S + 1))) < ε / 2 := by
    rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hLn : 0 ≤ Real.log ℓ ^ (e + 1) / ℓ :=
    div_nonneg (pow_nonneg (Real.log_nonneg (by linarith [Real.add_one_le_exp 1])) _)
      ((Real.exp_pos 1).trans_le hℓ2).le
  have f2 : S * (a * (Real.log ℓ ^ (e + 1) / ℓ)) < ε / 2 := by
    rw [← mul_assoc]
    calc S * a * (Real.log ℓ ^ (e + 1) / ℓ) ≤ (S * a + 1) * (Real.log ℓ ^ (e + 1) / ℓ) := by nlinarith
      _ < (S * a + 1) * (ε / (2 * (S * a + 1))) := mul_lt_mul_of_pos_left hℓ1 (by positivity)
      _ = ε / 2 := by field_simp
  linarith

end GlobalTheory.ArDegIndep.MixLimit

namespace GlobalTheory.ArDegIndep.MixLimit

open GlobalTheory.Mean4O.InterpFam

theorem comb_c1 {D : D7} {Y : ShimX D.what₂.Tau} (T : Real0 Y) (B : ℝ) (c : Y.Comp) (u : Wt Y) (g : (T.M c).Fun)
    (hg : (T.M c).Smooth g) (σ : Fin ((T.M c).n + 1)) {K : ℝ}
    (h : Comb ((T.M c).A σ) ((T.M c).Z σ) ((T.M c).r σ) ((T.M c).Om σ) K
      ((T.F c).th u σ + (LocPot.ofFun fun _ => (0 : ℝ)).rsmul 0 + LocPot.ofFun (g σ))) :
    Comb ((T.M c).A σ) ((T.M c).Z σ) ((T.M c).r σ) ((T.M c).Om σ) K ((T.K B c).c1 (T.L B c u + (T.K B c).ar g) σ) := by
  have lev : LeviEq ((T.M c).A σ) ((T.K B c).c1 (T.L B c u + (T.K B c).ar g) σ)
      ((T.F c).th u σ + (LocPot.ofFun fun _ => (0 : ℝ)).rsmul 0 + LocPot.ofFun (g σ)) := by
    intro j y hy w
    have pot := fun v => twice_differentiable_of_potential ((T.K B c).firstChern_isPotential v σ) hy
    have ht := twice_differentiable_of_potential (T.th_pot c u σ) hy
    have h0 := twice_differentiable_of_potential (isPotential_ofFun ((T.M c).A σ) (fun _ => (0 : ℝ)) fun _ => contDiffOn_const) hy
    have hgc := twice_differentiable_of_potential (isPotential_ofFun ((T.M c).A σ) _ (hg σ)) hy
    rw [(T.K B c).isOneCochain_add _ _ σ j y hy w, lv_add (pot _) (pot _), T.c1_L B c u σ j y hy w,
      (T.K B c).c1_ar g hg σ j y hy w, lv_add (ht.add (h0.rsmul 0)) hgc, lv_add ht (h0.rsmul 0), lv_rsmul h0,
      zero_mul, add_zero]
  obtain ⟨-, T', cc, h1, h2⟩ := h
  exact ⟨(T.K B c).firstChern_isPotential _ σ, T', cc, h1, fun j y hy hz w => (lev j y hy w).trans (h2 j y hy hz w)⟩

theorem mixed_limit : Hypotheses2 → HypothesesH → OnObj fun D O A T H h => ∀ x' : GlobalTheory.ShFam.ToroidalCompactificationData O.s, ∀ B : ℝ, 2 ≤ B → ∀ u : Wt O.Y, (∀ τ, StrictAnti (u τ)) → ∀ (c : O.Y.Comp) (i : ℕ), i ≤ dimY O.Y → Tendsto (fun R : ℝ => (T.M c).int (fun k : Fin (dimY O.Y) => (T.K B c).c1 (if (k : ℕ) < i then T.L B c u + (T.K B c).ar ((T.F c).phR R u) else T.L B c u + (T.K B c).ar (psiOf h x' R u c))) ((T.F c).phR R u - psiOf h x' R u c)) atTop (𝓝 0) := by
  intro hP2 hPH D O hcore hf A T H h x' B _ u hu c i _
  obtain ⟨hSize, hInR⟩ := GlobalTheory.T.fibre_size_and_range_bound hP2 hPH D O hcore hf A T H h c
  have hDomL : DomL O.Y.j u := fun τ a b hab _ => (hu τ (show a < b by rw [Fin.lt_def]; omega)).le
  obtain ⟨-, -, -, C₁, hC₁⟩ := hSize
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.T.green_correction_log_growth hP2 hPH D O hcore hf A T H h x' c
  choose b p hbp Cr hCr using hInR
  choose b' p' hbp' t' ht' using GlobalTheory.T.poincare_potential_psh_limit hP2 hPH D O hcore hf A T H h x' c u hu
  have smψ : ∀ R : ℝ, 2 ≤ R → (T.M c).Smooth (psiOf h x' R u c) := fun R hR =>
    GlobalTheory.T.smooth_potential_truncation hP2 hPH D O hcore hf A T H h x' R hR u c
  have smφ : ∀ R : ℝ, 2 ≤ R → (T.M c).Smooth ((T.F c).phR R u) := fun R hR σ => ((hCr σ) u R hR).1
  have hlogr : ∀ σ (x : (T.M c).X σ), x ∉ (T.M c).Z σ → 0 ≤ Real.log ((T.M c).r σ x) := fun σ x hx =>
    zero_le_one.trans (one_le_log ((T.M c).bd σ).2.2.2.2.2.1 hx)
  have bφ : ∀ R : ℝ, 2 ≤ R → ∀ σ x, x ∉ (T.M c).Z σ →
      |(T.F c).phR R u σ x| ≤ |C₁| * ‖u‖ * Real.log ((T.M c).r σ x) := fun R hR σ x hx =>
    ((hC₁ u σ x hx).2 R hR).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)) (hlogr σ x hx))
  have bψ : ∀ R : ℝ, 2 ≤ R → ∀ σ x, x ∉ (T.M c).Z σ →
      |psiOf h x' R u c σ x| ≤ |C₂| * ‖u‖ * Real.log ((T.M c).r σ x) := fun R hR σ x hx =>
    (hC₂ u σ x hx R hR).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)) (hlogr σ x hx))

  have key : ∀ σ, ∃ K₁ : ℝ, ∀ K, K₁ ≤ K → ∀ R : ℝ, 2 ≤ R →
      Comb ((T.M c).A σ) ((T.M c).Z σ) ((T.M c).r σ) ((T.M c).Om σ) K
        ((T.F c).th u σ + (LocPot.ofFun fun _ => (0 : ℝ)).rsmul 0 + LocPot.ofFun ((T.F c).phR R u σ)) := by
    intro σ
    have hbd := (T.M c).bd σ
    obtain ⟨K₀, hK₀, hth⟩ := exists_lvBd hbd.2.2.1 hbd.2.2.2.1 (T.th_pot c u σ)
    have h0 : ((T.M c).A σ).Smooth fun _ => (0 : ℝ) := fun _ => contDiffOn_const
    obtain ⟨K₁, hK₁⟩ := comb_one hbd (isPotential_ofFun _ _ h0) (fun _ j y _ w => (lv_zero (A := (T.M c).A σ) j y w).ge) (hbp σ) K₀
      (|C₁| * ‖u‖) (|Cr σ| * ‖u‖) hK₀ (by positivity) (by positivity)
    refine ⟨K₁, fun K hK R hR => hK₁ K hK _ _ _ (T.th_pot c u σ) hth (smφ R hR σ) (bφ R hR σ)
      (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)) (((hCr σ) u R hR).2.1 hDomL) 0
      ⟨le_rfl, zero_le_one⟩⟩
  have key' : ∀ σ, ∃ K₁ : ℝ, ∀ K, K₁ ≤ K → ∀ᶠ R in atTop,
      Comb ((T.M c).A σ) ((T.M c).Z σ) ((T.M c).r σ) ((T.M c).Om σ) K
        ((T.F c).th u σ + (LocPot.ofFun fun _ => (0 : ℝ)).rsmul 0 + LocPot.ofFun (psiOf h x' R u c σ)) := by
    intro σ
    have hbd := (T.M c).bd σ
    obtain ⟨K₀, hK₀, hth⟩ := exists_lvBd hbd.2.2.1 hbd.2.2.2.1 (T.th_pot c u σ)
    have h0 : ((T.M c).A σ).Smooth fun _ => (0 : ℝ) := fun _ => contDiffOn_const
    obtain ⟨K₁, hK₁⟩ := comb_one hbd (isPotential_ofFun _ _ h0) (fun _ j y _ w => (lv_zero (A := (T.M c).A σ) j y w).ge) (hbp' σ) K₀
      (|C₂| * ‖u‖) |t' σ| hK₀ (by positivity) (abs_nonneg _)
    refine ⟨K₁, fun K hK => ?_⟩
    filter_upwards [ht' σ, eventually_ge_atTop 2] with R hR hR2
    exact hK₁ K hK _ _ _ (T.th_pot c u σ) hth (smψ R hR2 σ) (bψ R hR2 σ) (le_abs_self _) hR 0 ⟨le_rfl, zero_le_one⟩
  choose K₁ hK₁ using key
  choose K₂ hK₂ using key'
  set K : ℝ := ∑ σ, (|K₁ σ| + |K₂ σ|) with hK
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun σ _ => by positivity
  have hle : ∀ σ, |K₁ σ| + |K₂ σ| ≤ K := fun σ =>
    Finset.single_le_sum (f := fun σ => |K₁ σ| + |K₂ σ|) (fun _ _ => by positivity) (Finset.mem_univ σ)
  have hle1 : ∀ σ, K₁ σ ≤ K := fun σ => by linarith [le_abs_self (K₁ σ), abs_nonneg (K₂ σ), hle σ]
  have hle2 : ∀ σ, K₂ σ ≤ K := fun σ => by linarith [le_abs_self (K₂ σ), abs_nonneg (K₁ σ), hle σ]
  refine int_tendsto_zero (T.M c) K hK0
    (fun σ => GlobalTheory.T.mixed_integral_tail_bound_exists _ _ ((T.M c).A σ) ((T.M c).Z σ) ((T.M c).r σ) ((T.M c).Om σ) ((T.M c).bd σ) K) _ _
    ((|C₁| + |C₂|) * ‖u‖) (by positivity) ?_ ?_ ?_ ?_
  · filter_upwards [eventually_ge_atTop 2, Filter.eventually_all.2 fun σ => hK₂ σ K (hle2 σ)] with R hR hψ
    intro k σ
    split_ifs
    · exact comb_c1 T B c u _ (smφ R hR) σ (hK₁ σ K (hle1 σ) R hR)
    · exact comb_c1 T B c u _ (smψ R hR) σ (hψ σ)
  · filter_upwards [eventually_ge_atTop 2] with R hR
    intro σ
    exact st_smooth_continuous _ (fun l => ContDiffOn.sub (smφ R hR σ l) (smψ R hR σ l))
  · filter_upwards [eventually_ge_atTop 2] with R hR
    intro σ x hx
    show |(T.F c).phR R u σ x - psiOf h x' R u c σ x| ≤ _
    refine (abs_sub _ _).trans ?_
    have := bφ R hR σ x hx
    have := bψ R hR σ x hx
    nlinarith
  · intro ℓ δ hδ
    have hS : Tendsto (fun R : ℝ => (∑ σ, |Cr σ|) * ‖u‖ / R) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    filter_upwards [GlobalTheory.T.green_correction_converges_locally hP2 hPH D O hcore hf A T H h x' c u ℓ (δ / 2) (by positivity),
      (tendsto_order.1 hS).2 (δ / 2) (by positivity), eventually_ge_atTop (max 2 (ℓ ^ 2))] with R hψ hR hR2
    intro σ x hx hr
    have hR2' : 2 ≤ R := (le_max_left _ _).trans hR2
    have hsq : (T.M c).r σ x ≤ Real.sqrt R := by
      refine hr.trans ((le_abs_self ℓ).trans ?_)
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt ((le_max_right _ _).trans hR2)
    have e1 := ((hCr σ) u R hR2').2.2 x hx |>.2 hsq
    have e2 := hψ σ x hx hr
    have hR0 : 0 < R := by linarith
    have e3 : Cr σ * ‖u‖ / R ≤ (∑ σ, |Cr σ|) * ‖u‖ / R := by
      gcongr
      exact (le_abs_self _).trans (Finset.single_le_sum (f := fun σ => |Cr σ|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ σ))
    show |(T.F c).phR R u σ x - psiOf h x' R u c σ x| ≤ δ
    have : (T.F c).phR R u σ x - psiOf h x' R u c σ x =
        ((T.F c).phR R u σ x - (T.F c).ph u σ x) - (psiOf h x' R u c σ x - (T.F c).ph u σ x) := by ring
    rw [this]
    refine (abs_sub _ _).trans ?_
    linarith

end GlobalTheory.ArDegIndep.MixLimit
