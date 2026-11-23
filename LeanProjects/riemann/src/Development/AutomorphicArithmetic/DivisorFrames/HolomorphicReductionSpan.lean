import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.FamArc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsExtendVanishCompactifiedFlagSpace
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal GlobalTheory.KoecherArc

private theorem comb_quot {m : ℕ} (ε : Fin m → ℂ) (f p q : Fin m → ℂ → ℂ) (s : Set ℂ)
    (hp : ∀ i, DifferentiableOn ℂ (p i) s) (hq : ∀ i, DifferentiableOn ℂ (q i) s)
    (h : ∀ i, ∀ u ∈ s, u ≠ 0 → q i u ≠ 0 ∧ f i u * q i u = p i u) :
    ∃ a b : ℂ → ℂ, DifferentiableOn ℂ a s ∧ DifferentiableOn ℂ b s ∧
      ∀ u ∈ s, u ≠ 0 → b u ≠ 0 ∧ (∑ i, ε i * f i u) * b u = a u := by
  classical
  refine ⟨fun u => ∑ i, ε i * p i u * ∏ k ∈ Finset.univ.erase i, q k u, fun u => ∏ i, q i u, ?_, ?_, ?_⟩
  · exact DifferentiableOn.fun_sum fun i _ => ((hp i).const_mul _).mul
      (DifferentiableOn.fun_finsetProd fun k _ => hq k)
  · exact DifferentiableOn.fun_finsetProd fun k _ => hq k
  · intro u hu h0
    refine ⟨Finset.prod_ne_zero_iff.2 fun i _ => (h i u hu h0).1, ?_⟩
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    beta_reduce
    rw [← Finset.mul_prod_erase Finset.univ (fun k => q k u) (Finset.mem_univ i), ← (h i u hu h0).2]
    ring

private theorem tendsto_fam {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β)
    {σ : c.F →+* ℂ} {N : ℕ} {U : Unf Xo c σ N} (hσ : GoodEmb c σ) (hU : IsUnf U) (la : ∀ k, Wt (U.X k).Ψ N)
    (hχ : ∀ k, ∀ γ ∈ (U.X k).Γ, (U.X k).χ (la k) γ = 1) {e : Ix Dw → ℤ} (he : e none = 0)
    {n : ℕ} (ε : Fin n → ℂ) (g : Fin n → AllWt.secZ Xo c e)
    (hS : ∀ k, (∑ i, ε i • rdU U (g i : Rul Xo c)) k ∈ (U.X k).SS (la k)) {A : Type} [CommRing A] {φ : c.F →+* A}
    {x : Sp A ⟶ gen Z} (fr : EigFrame Z φ (x ≫ genι Z)) {ψ : ℂ → (A →+* ℂ)} {r : ℝ} {y : ℂ → FrPt Xo c (CAt σ)}
    (hb : IsBdArc Z σ φ x ψ r) (hm : ∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → Matches fr (ψ u) (y u)) (a b : ℂ → ℂ)
    (ha : DifferentiableOn ℂ a (Metric.ball 0 r)) (hb' : DifferentiableOn ℂ b (Metric.ball 0 r))
    (hpq : ∀ u ∈ Metric.ball (0 : ℂ) r, u ≠ 0 → b u ≠ 0 ∧
      (∑ i, ε i * toC (evR Xo c (g i : Rul Xo c) (y u))) * b u = a u) :
    Tendsto (fun u => ∑ i, ε i * toC (evR Xo c (g i : Rul Xo c) (y u))) (𝓝[≠] 0) (𝓝 0) := by
  haveI : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
  obtain ⟨k, T, M₀, γ₀, xx, hT, hO₀, hL⟩ := GlobalTheory.T.exists_holomorphicFrameOrbit_lift_of_arc E H Dw l Xo c O β Z σ N U A φ x fr ψ r y hσ hU hb.1 hm
  obtain ⟨M, γ, hO, hγ⟩ := GlobalTheory.T.exists_holomorphicFrameOrbit_unipotent_order_two E N _ T M₀ γ₀ xx hO₀
  have hne : γ ≠ 1 := by
    rintro rfl
    obtain ⟨x₀, hx₀, x', h1, h2⟩ := GlobalTheory.T.trivial_monodromy_orbit_converges_symmetric_domain E N _ T M xx hO
    exact GlobalTheory.T.boundary_arc_lift_not_converges_symmetric_domain E H Dw l Xo c O β Z σ N U A φ x fr ψ r y k T xx hσ hU hb hm hL x₀ hx₀ x' h1 h2
  obtain ⟨ξ, c', hξ, hc', ht⟩ := GlobalTheory.T.holomorphicFrameOrbit_isotropic_vector_short E N _ T M γ xx hO hγ hne
  obtain ⟨m, v, Lp, Lm, hlim⟩ :=
    GlobalTheory.T.exists_arcLift_periods_tendsto_span E H Dw l Xo c O β Z σ N U A φ x fr ψ r y k T M γ xx hσ hU hb.1 hm hO hL
  have hper := GlobalTheory.T.eigenframe_specialization_uniform_bound E H Dw l Xo c O β Z σ N U A φ x fr ψ r y k T M γ xx hσ hU hb.1 hm hO hL
  obtain ⟨C', B, hn⟩ := GlobalTheory.T.normFactor_inv_le_pow_holomorphicOrbit_periodBound E N _ T M γ xx (la k) m v Lp Lm hO hlim hper
  have hp := tendsto_cusp (hS k) hO.2.2.2.1 hξ hc' ht hn
  have hsec := (hS k).1.1
  obtain ⟨hM, hΓ, hdiff, hdom, hperd⟩ := hO
  have hγd : ∀ w : ℂ, T < w.im → lact γ (xx w) ∈ (U.X k).dom := fun w hw =>
    GlobalTheory.MajInv.lact_mem_dom _ ((U.X k).Γ_stab γ hΓ) (hdom w hw)
  refine GlobalTheory.T.meromorphic_germ_vanishes_of_periodic_exp_modulus (fun w => (∑ i, ε i • rdU U (g i : Rul Xo c)) k (xx w)) (fun _ => 0) _ a b T r M 1 1 hM
    one_pos (one_pow 1) hb.1.1.1 (hsec.1.comp hdiff hdom) (differentiableOn_const 0) (fun w hw => ?_) hp
    ha hb' hpq
  obtain ⟨b, hb1, hb2, hb3⟩ := hperd w hw
  obtain ⟨h, hl⟩ := hL w hw
  refine ⟨?_, rfl, ?_⟩
  · simp only [hb3]
    rw [hsec.2.1 _ (hγd w hw) b hb1, hsec.2.2 γ hΓ _ (hdom w hw), hχ k γ hΓ]
    simp [ReciprocityTheory.ChartRestriction.G.FD.bchar, hb2]
  · rw [Complex.exp_zero, norm_one, mul_one]
    have rd : ∀ i, rdU U (g i : Rul Xo c) k (xx w) = toC (evR Xo c (g i : Rul Xo c) (y (eTwoPi w))) := fun i => by
      have rd : rdU U (g i : Rul Xo c) k (xx w) = toC (evR Xo c (g i : Rul Xo c) (U.un k ⟨xx w, h⟩)) := dif_pos h
      rw [rd, GlobalTheory.ShFam.KeyRel.evR_sameLie he (g i).2 hl]
    show ‖∑ i, ε i * toC (evR Xo c (g i : Rul Xo c) (y (eTwoPi w)))‖ = ‖(∑ i, ε i • rdU U (g i : Rul Xo c)) k (xx w)‖
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, rd]

private theorem exists_radius {m : ℕ} (ρ : Fin m → ℝ) (r : ℝ) (hr : 0 < r) (hρ : ∀ i, 0 < ρ i) :
    ∃ s : ℝ, 0 < s ∧ s ≤ r ∧ ∀ i, s ≤ ρ i := by
  induction m with
  | zero => exact ⟨r, hr, le_rfl, fun i => i.elim0⟩
  | succ m ih =>
    obtain ⟨s, h1, h2, h3⟩ := ih (fun i => ρ i.succ) fun i => hρ _
    exact ⟨min s (ρ 0), lt_min h1 (hρ 0), (min_le_left _ _).trans h2,
      Fin.cases (min_le_right _ _) fun i => (min_le_left _ _).trans (h3 i)⟩

private theorem famArcZero_cusp :
    ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : GlobalTheory.CompHS.TorFlag Y.d.Xo₂ Y.d.c₂) (la : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (σ : Y.d.c₂.F →+* ℂ), GoodEmb Y.d.c₂ σ → ∀ (m : ℕ) (ε : Fin m → ℂ) (g : Fin m → AllWt.secZ Y.d.Xo₂ Y.d.c₂ (AllWt.exOf (T.Q.Dw j) la 0)), (∀ k, (∑ i, ε i • rdU (Y.U σ) (g i : Rul Y.d.Xo₂ Y.d.c₂)) k ∈ ((Y.U σ).X k).SS (AllWt.modelWt (Y.U σ) (wtOf (T.Q.Dw j) la 0) k)) → GlobalTheory.CompHS.FamArcZero TF.X Z la σ ε (fun i => GlobalTheory.CompHS.sec₀ TF.X Z _ (g i)) := by
  intro D T j Y e o hY Z TF la σ hσ m ε g hS
  haveI : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
  have hU := hY.unf σ hσ
  have hχ := AllWt.Model.chi_modelWt (Y.U σ) (hY.chiTriv σ hσ) (AllWt.wtOf _ la 0) (AllWt.even_wtOf la 0)
  have he : AllWt.exOf (T.Q.Dw j) la 0 none = 0 := by
    show (AllWt.wtOf (T.Q.Dw j) la 0).2 = 0
    rw [AllWt.wtOf_snd, mul_zero]
  intro W hW i hWi ψ r hψ hs hin hout η hη
  obtain ⟨φ, x, fr, y, hb, hm, hval⟩ := GlobalTheory.T.exists_eigenFrame_along_arc_flagSpaceChart TF Z la σ hσ W hW i hWi ψ r hψ hs hin hout
  choose ρ' p q hρ' hρr' hpq using fun t : Fin m =>
    GlobalTheory.T.exists_holomorphic_quotient_along_arc (sec₀ TF.X Z _ (g t)) W hW i hWi ψ r hψ hout
  obtain ⟨ρ, hρ, hρr, hρρ⟩ := exists_radius ρ' r hψ.1 hρ'
  have hi : ∀ u, ⊤ ≤ (spMap (ψ u) ≫ (show Sp Γ(Y₀ TF.X Z, W) ⟶ Y₀ TF.X Z from hW.fromSpec)) ⁻¹ᵁ
      (L₀ TF.X Z la).U i := fun u s _ => hWi (hW.range_fromSpec.le ⟨_, rfl⟩)
  have hv : ∀ t, ∀ u ∈ Metric.ball (0 : ℂ) ρ, u ≠ 0 →
      ψ u (q t) ≠ 0 ∧ toC (evR _ _ (g t).1 (y u)) * ψ u (q t) = ψ u (p t) :=
    fun t u hu h => by
      have hur : u ∈ Metric.ball (0 : ℂ) r := Metric.ball_subset_ball hρr hu
      have hut : u ∈ Metric.ball (0 : ℂ) (ρ' t) := Metric.ball_subset_ball (hρρ t) hu
      refine ⟨(hpq t u hut h).1, ?_⟩
      rw [← hval (g t) u hur h (hout u hur h) (hi u)]
      exact (hpq t u hut h).2 _ _
  obtain ⟨a, b, ha, hb', hab⟩ := comb_quot ε (fun t u => toC (evR _ _ (g t).1 (y u))) (fun t u => ψ u (p t))
    (fun t u => ψ u (q t)) (Metric.ball 0 ρ) (fun t => (hψ.2 (p t)).mono (Metric.ball_subset_ball hρr))
    (fun t => (hψ.2 (q t)).mono (Metric.ball_subset_ball hρr)) hv
  have ht := tendsto_fam TF.Y hσ hU _ hχ he ε g hS fr (isBdArc_mono hb hρ hρr)
    (fun u hu h => hm u (Metric.ball_subset_ball hρr hu) h) a b ha hb' hab
  have h2 : Tendsto (fun u => ‖∑ t, ε t * toC (evR _ _ (g t).1 (y u))‖) (𝓝[≠] 0) (𝓝 0) := by simpa using ht.norm
  filter_upwards [h2.eventually (gt_mem_nhds hη), self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℂ) hρ)] with u h1 h3 h4 hO hi'
  rw [Finset.sum_congr rfl fun t _ => congrArg (ε t * ·)
    (hval (g t) u (Metric.ball_subset_ball hρr h4) h3 hO hi')]
  exact h1

end

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

theorem UpperTheory.holomorphic_reduction_span :
    ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : GlobalTheory.CompHS.TorFlag Y.d.Xo₂ Y.d.c₂) (la : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (σ : Y.d.c₂.F →+* ℂ), GoodEmb Y.d.c₂ σ → ∀ (m : ℕ) (ε : Fin m → ℂ) (g : Fin m → secZ Y.d.Xo₂ Y.d.c₂ (exOf (T.Q.Dw j) la 0)), (∑ i, ε i • rdU (Y.U σ) (g i : Rul Y.d.Xo₂ Y.d.c₂)) ∈ holSub (Y.U σ).X (modelWt (Y.U σ) (wtOf (T.Q.Dw j) la 0)) → GlobalTheory.CompHS.FamArcZero TF.X Z la σ ε (fun i => GlobalTheory.CompHS.sec₀ TF.X Z _ (g i)) := by
  intro D T j Y e o hY Z TF la σ hσ m ε g h
  exact famArcZero_cusp D T j Y e o hY Z TF la σ hσ m ε g (GlobalTheory.CuspSecFin.mem_SS_of_mem_holSub _ _ h)
