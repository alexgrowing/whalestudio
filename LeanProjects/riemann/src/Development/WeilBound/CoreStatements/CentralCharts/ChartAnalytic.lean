import Development.WeilBound.CoreStatements.CentralCharts.AnalyticAtEval
import Development.WeilBound.CoreStatements.CentralCharts.PshAt0LogNorm
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagWeightedDegreeSection
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootLinesFlagDegreeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GlobalPairSumGramBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixChangeFrameStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameDomainInSegreChartStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentresStatement

noncomputable section

namespace AnalyticReference.An

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree
open Filter Topology
open scoped ComplexOrder

theorem frame_sup {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {V : Type}
    [AddCommGroup V] [Module Ω V] (L : Lat ξ V) (W : Submodule Ω V) {r : ℕ} (bb : Fin r → W) (p : Cpt ξ)
    (hb : L.IsFrameAt (fun k => (bb k : V)) p) : (Lat.comap (fun p => L p ⊔ L p) W.subtype).IsFrameAt bb p := by
  have hspan : (Submodule.span (regAt ξ p) (Set.range bb)).map (W.subtype.restrictScalars (regAt ξ p)) =
      Submodule.span (regAt ξ p) (Set.range fun k => (bb k : V)) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  refine ⟨LinearIndependent.of_comp W.subtype hb.1, ?_⟩
  ext x
  constructor
  · intro hx
    have h1 : (x : V) ∈ L p ⊔ L p := hx
    rw [sup_idem, hb.2, ← hspan] at h1
    obtain ⟨x', hx', e⟩ := h1
    have e' : x' = x := Subtype.ext e
    exact e' ▸ hx'
  · intro hx
    show (x : V) ∈ L p ⊔ L p
    rw [sup_idem, hb.2, ← hspan]
    exact ⟨x, hx, rfl⟩

theorem chart_analytic {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {P : Ideal (MRing J)} {n : ℕ}
    {Bd : Set ((Σ k, J k) → ℂ)} (χ : SncChart P n Bd) (q : Σ k, J k) : AnalyticAt ℂ (fun t => χ.γ t q) 0 :=
  ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, J k) => ℂ) q).analyticAt _).comp
    (χ.analytic 0 (Metric.mem_ball_self one_pos))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {Xo : ∀ l : Tor.Level H, Moduli D l} {l : Tor.Level H} {c : Coeff l} [NumberField c.F]
  {Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω] [CharZero Ω]
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem label_data (hG : Top.Given) (hGl : Top.IsGlobal Xo l c Y) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) {n : ℕ}
    {Bd : Set ((Σ k, J k) → ℂ)}
    (hBd : ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ y z w → (w ∈ Bd ↔ ¬ 𝔐.Interior z))
    (χ : SncChart (mCoordIdeal y) n Bd) {z₀ : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X} (hz₀ : CoordsAt 𝔐.ξ y z₀ (χ.γ 0))
    (s : CMType H ⊕ CMType H) :
    ∃ (b : Fin (labelRk D s) → 𝔐.Li) (M : ℕ → (Fin n → ℂ) → ℝ),
      (∀ j, flagStep Ω b j = flagStep Ω (Fl.b s) j) ∧ (𝔐.V s).IsFrameAt b ⟨centre z₀, 𝔐.all _⟩ ∧
      (∀ t, M 0 t = 0) ∧ (∀ m ≤ labelRk D s, Tame χ.a (M m) ∧ (χ.a = 0 → PshAt0 (M m))) ∧
      ∀ᶠ t in 𝓝 (0 : Fin n → ℂ), (∀ i : Fin n, (i : ℕ) < χ.a → t i ≠ 0) →
        ∀ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z (χ.γ t) → 𝔐.Interior z ∧
          (𝔐.V s).IsFrameAt b ⟨centre z, 𝔐.all _⟩ ∧ ∃ Γ, 𝔐.M.GramAt 𝔐.t.PP.L z b Γ ∧ Γ.PosDef ∧
            ∀ m ≤ labelRk D s, Real.log (leadMinor Γ m) = M m t := by
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  have hgen : genPt 𝔐.ξ ⤳ centre z₀ := 𝔐.all _
  obtain ⟨V, hV, b, hflag, hb⟩ := Fl.sub s ⟨centre z₀, hgen⟩ trivial
  have hb0 := hb ⟨centre z₀, hgen⟩ trivial hV
  obtain ⟨cc, f, hdom, -, hsub⟩ := exists_basic 𝔐.tie hz₀ hgen V hV
  obtain ⟨hVd, -, -⟩ := GlobalTheory.T.hodge_cpt_away_from_primes E H D l (Xo l) c _ _ Y S Ω K J y 𝔐 hβ ⟨centre z₀, hgen⟩
    fun r hr => GrNorm.not_inFibre 𝔐.tie.gen hgen hr
  have hmem : ∀ k, b k ∈ 𝔐.Vgen s ⊔ 𝔐.Vgen s := fun k => by
    have h1 : b k ∈ 𝔐.V s ⟨centre z₀, hgen⟩ := by
      rw [hb0.2]
      exact Submodule.subset_span ⟨k, rfl⟩
    rw [hVd s] at h1
    exact Submodule.mem_sup_left h1.2
  let bb : Fin (labelRk D s) → ↥(𝔐.Vgen s ⊔ 𝔐.Vgen s) := fun k => ⟨b k, hmem k⟩
  obtain ⟨a₀, g, Λ, _, L, π, ρ, U, hρ, hρ1, hU, hli, ha, hP⟩ :=
    GlobalTheory.T.global_pair_sum_gram_bound hG E H D Xo l c Y S Ω K J y 𝔐 hGl s s _ bb n Bd χ 0 cc f hBd (Metric.mem_ball_self one_pos)
      (fun p h1 h2 => frame_sup (𝔐.V s) _ bb p (hb p trivial (hsub p h1 h2))) hdom
  let M : ℕ → (Fin n → ℂ) → ℝ := fun m t =>
    Real.log (leadMinor (HodgeMetric.periodGram L U (HodgeMetric.uncentre 0 ρ π t)) m)
  have hM : ∀ m (h : m ≤ labelRk D s), M m = fun t => Real.log
      (HodgeMetric.periodGram L (fun j => U (Fin.castLE h j)) (HodgeMetric.uncentre 0 ρ π t)).det.re := by
    intro m h
    funext t
    simp only [M, leadMinor, dif_pos h]
    rfl
  refine ⟨b, M, hflag, hb0, fun t => by simp [M, leadMinor_size_zero], fun m hm => ?_, ?_⟩
  · rw [hM m hm]
    have hli' : LinearIndependent ℂ fun j : Fin m => U (Fin.castLE hm j) 0 := hli.comp _ (Fin.castLE_injective hm)
    refine ⟨tame_logdet L _ π ρ hρ hρ1 (fun j => hU _) hli' fun i hi => (ha i hi).1, fun h0 => ?_⟩
    have : a₀ = 0 := by
      by_contra hne
      have hle := L.a_le
      have := (ha ⟨0, by omega⟩ (Nat.pos_of_ne_zero hne)).1
      omega
    subst this
    exact pshAt0_logdet L _ π ρ hρ (fun j => hU _) hli'
  · filter_upwards [Metric.ball_mem_nhds (0 : Fin n → ℂ) hρ] with t ht hoff z hz
    have hu := HodgeMetric.uncentre_mem_ball (t₀ := 0) (t := t) hρ π (by simpa using ht)
    obtain ⟨h1, h2, h3, h4⟩ := hP _ hu
    rw [HodgeMetric.recentre_uncentre 0 hρ π t] at h1 h2 h3 h4
    have hnb : χ.γ t ∉ Bd := fun h => by
      obtain ⟨i, hi, h0⟩ := (χ.boundary t h1).1 h
      exact hoff i hi h0
    have hi : 𝔐.Interior z := by_contra fun h => hnb ((hBd z _ hz).2 h)
    have hc := GlobalTheory.T.frame_domain_in_segre_chart 𝔐.X Ω 𝔐.ξ K J y 𝔐.tie z _ cc f (𝔐.all _) hz h2
    have hfr := hb _ trivial (hsub _ hc.1 hc.2)
    have hΓ := h4 (h3.1 hnb) z hz
    obtain ⟨Γ, g1, g2⟩ := RootGram.exists_gram 𝔐 hi s hfr
    have e := GlobalTheory.T.gram_matrix_change_frame E H D l (Xo l) c Y S Ω K J y 𝔐 z _ b _ _
      (GlobalTheory.T.interior_point_polarised E H D l (Xo l) c Y S Ω K J y 𝔐 z hi) g1 hΓ
    refine ⟨hi, hfr, Γ, g1, g2, fun m _ => ?_⟩
    rw [e]

theorem root_data (hG : Top.Given) (hGl : Top.IsGlobal Xo l c Y) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) {n : ℕ}
    {Bd : Set ((Σ k, J k) → ℂ)}
    (hBd : ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ y z w → (w ∈ Bd ↔ ¬ 𝔐.Interior z))
    (χ : SncChart (mCoordIdeal y) n Bd) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ)
    (e : CMType H × Fin (D.p + D.q) → Ω) (hx : CMType H × Fin (D.p + D.q) → HermLine J) (hroot : Fl.RootLines xdeg e)
    (hhod : ∀ r, Fl.IsHodgeLine r (e r) (hx r)) (hdg : ∀ r, (hx r).a = xdeg r) :
    ∃ (M : CMType H ⊕ CMType H → ℕ → (Fin n → ℂ) → ℝ) (F : CMType H × Fin (D.p + D.q) → (Fin n → ℂ) → ℂ),
      (∀ s t, M s 0 t = 0) ∧ (∀ s, ∀ m ≤ labelRk D s, Tame χ.a (M s m) ∧ (χ.a = 0 → PshAt0 (M s m))) ∧
      (∀ r, AnalyticAt ℂ (F r) 0 ∧ F r 0 ≠ 0) ∧
      ∀ r, ∀ᶠ t in 𝓝 (0 : Fin n → ℂ), (∀ i : Fin n, (i : ℕ) < χ.a → t i ≠ 0) →
        Real.log ((hx r).h (χ.γ t)) = Real.log ‖F r t‖ - (HodgeCpt.rootSgn D r : ℝ) / 2 *
          (M (HodgeCpt.rootIdx D r).1 (((HodgeCpt.rootIdx D r).2 : ℕ) + 1) t -
            M (HodgeCpt.rootIdx D r).1 ((HodgeCpt.rootIdx D r).2 : ℕ) t) := by
  have pts : ∀ w ∈ mcPts (mCoordIdeal y), ∃ z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X, CoordsAt 𝔐.ξ y z w := fun w hw => by
    obtain ⟨z, -, hz⟩ := (GlobalTheory.T.complex_points_iff_centres 𝔐.X Ω 𝔐.ξ K J y 𝔐.tie w).1 hw
    exact ⟨z, hz⟩
  obtain ⟨z₀, hz₀⟩ := pts _ (χ.mem 0 (Metric.mem_ball_self one_pos))
  have hgen : genPt 𝔐.ξ ⤳ centre z₀ := 𝔐.all _
  choose b M hflag hb0 hM0 hM hev using label_data hG hGl 𝔐 Fl hBd χ hz₀
  obtain ⟨cc, f, hdom, hch, -⟩ := exists_basic 𝔐.tie hz₀ hgen ⊤ trivial
  have hcc : ∀ᶠ t in 𝓝 (0 : Fin n → ℂ), ∀ k, χ.γ t ⟨k, cc k⟩ ≠ 0 :=
    eventually_all.2 fun k => (chart_analytic χ _).continuousAt.eventually_ne (hdom.1 k)
  have key : ∀ r : CMType H × Fin (D.p + D.q), ∃ F : (Fin n → ℂ) → ℂ, (AnalyticAt ℂ F 0 ∧ F 0 ≠ 0) ∧
      ∀ᶠ t in 𝓝 (0 : Fin n → ℂ), (∀ i : Fin n, (i : ℕ) < χ.a → t i ≠ 0) →
        Real.log ((hx r).h (χ.γ t)) = Real.log ‖F t‖ - (HodgeCpt.rootSgn D r : ℝ) / 2 *
          (M (HodgeCpt.rootIdx D r).1 (((HodgeCpt.rootIdx D r).2 : ℕ) + 1) t -
            M (HodgeCpt.rootIdx D r).1 ((HodgeCpt.rootIdx D r).2 : ℕ) t) := by
    intro r
    obtain ⟨τ, hτ⟩ := GrNorm.exists_sub_mem_flagStep (b := Fl.b (HodgeCpt.rootIdx D r).1) (HodgeCpt.rootIdx D r).2
      (x := b _ (HodgeCpt.rootIdx D r).2) (by
        rw [← hflag]
        exact Submodule.subset_span ⟨_, Nat.lt_succ_self _, rfl⟩)
    have hu := GlobalTheory.T.root_lines_flag_degree E H D l (Xo l) c Y S Ω K J y 𝔐 Fl xdeg e r _ cc _ τ hroot hch (hflag _) (hb0 _) hτ
    obtain ⟨v, hv0, hv⟩ := exists_val_ne hgen hu
    have hv' := CxVal.inv hv hv0
    rw [inv_div] at hv'
    obtain ⟨F₁, hF₁, hF0, hF⟩ := exists_val_fam 𝔐.tie 𝔐.all (chart_analytic χ) hz₀ hv'
    have hne : F₁ 0 * ∏ k, χ.γ 0 ⟨k, cc k⟩ ^ xdeg r k ≠ 0 :=
      mul_ne_zero (by rw [hF0]; exact inv_ne_zero hv0)
        (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hdom.1 k))
    refine ⟨fun t => F₁ t * ∏ k, χ.γ t ⟨k, cc k⟩ ^ xdeg r k, ⟨hF₁.fun_mul
      (Finset.analyticAt_fun_prod _ fun k _ => (chart_analytic χ _).fun_zpow (hdom.1 k)), hne⟩, ?_⟩
    filter_upwards [hev (HodgeCpt.rootIdx D r).1, hF, hcc, Metric.ball_mem_nhds (0 : Fin n → ℂ) one_pos] with
      t h1 h2 h3 h4 hoff
    obtain ⟨z, hz⟩ := pts _ (χ.mem t h4)
    obtain ⟨hi, hfr, Γ, g1, g2, g3⟩ := h1 hoff z hz
    have hN := hhod r z _ hz hi τ _ ⟨𝔐.all _, _, Γ, hflag _, hfr, hτ, g1, g2, rfl⟩
    obtain ⟨u, hu1, hu2⟩ := hN.2.2 cc h3
    rw [hdg] at hu1 hu2
    rw [CxVal.unique hu1 (h2 z hz)] at hu2
    have p1 := leadMinor_pos_of_posDef g2 (s := ((HodgeCpt.rootIdx D r).2 : ℕ) + 1) (HodgeCpt.rootIdx D r).2.2
    have p2 := leadMinor_pos_of_posDef g2 (s := ((HodgeCpt.rootIdx D r).2 : ℕ)) (HodgeCpt.rootIdx D r).2.2.le
    have p3 : 0 < (hx r).h (χ.γ t) := (hx r).pos _ fun k => ⟨cc k, h3 k⟩
    have e1 := congrArg Real.log hu2
    rw [Real.log_mul (zpow_ne_zero _ (Real.sqrt_pos.2 (div_pos p1 p2)).ne') p3.ne', Real.log_zpow,
      Real.log_sqrt (div_pos p1 p2).le, Real.log_div p1.ne' p2.ne', g3 _ (HodgeCpt.rootIdx D r).2.2,
      g3 _ (HodgeCpt.rootIdx D r).2.2.le] at e1
    simp only [norm_mul, norm_prod, norm_zpow]
    rw [← e1]
    ring
  choose F hF hF' using key
  exact ⟨M, F, hM0, hM, hF, hF'⟩

end AnalyticReference.An
