import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsPhiNormSq
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspIntersectionPositive
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspIntersectionPositiveStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannFormLowerBoundNearCuspStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PshLogGrowthBoundedNearPunctureStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cusp.CorrBdd

open ReciprocityTheory.AnForm.A (IsPsh)
open _root_.Metric GlobalTheory.CompanionTheory.Ar.Cusp.CuspCorrespondence GlobalTheory.CompanionTheory.Ar.Cusp.CorrPsh
open LevelTowerAlt (lower_centre)
open GroundTheory.Heights₂.Heights.Regular (logCover expCover)

theorem exists_lift {n a : ℕ} (h : a ≤ n) {z : Fin n → ℂ} (hz : z ∈ Flat.punct n a 1) :
    ∃ w ∈ logCover h, expCover a w = z := by
  have h1 : ∀ k, ‖z k‖ < 1 := (pi_norm_lt_iff one_pos).1 (mem_ball_zero_iff.1 hz.1)
  refine ⟨fun k => if k.val < a then Complex.log (z k) else z k, ⟨fun i => ?_, fun k hk => ?_⟩, ?_⟩
  · have hi : (Fin.castLE h i).val < a := i.isLt
    simp only [if_pos hi, Complex.log_re]
    exact Real.log_neg (norm_pos_iff.mpr (hz.2 _ hi)) (h1 _)
  · simp only [if_neg (not_lt.mpr hk)]
    exact h1 k
  · funext k
    by_cases hk : k.val < a
    · simp only [expCover, if_pos hk, Complex.exp_log (hz.2 k hk)]
    · simp only [expCover, if_neg hk]

theorem isPsh_comp_aff {n : ℕ} (t₀ : Fin n → ℂ) (ρ : ℝ) (π : Equiv.Perm (Fin n)) {U V : Set (Fin n → ℂ)}
    {f : (Fin n → ℂ) → ℝ} (h : IsPsh V f) (hUV : ∀ u ∈ U, aff t₀ ρ π u ∈ V) :
    IsPsh U fun u => f (aff t₀ ρ π u) := by
  have hc : Continuous (aff t₀ ρ π) := by
    unfold aff
    fun_prop
  have ha : ∀ (z w : Fin n → ℂ) (ζ : ℂ), aff t₀ ρ π (z + ζ • w) = aff t₀ ρ π z + ζ • ((ρ : ℂ) • (w ∘ π)) := by
    intro z w ζ
    funext i
    simp [aff]
    ring
  refine ⟨h.1.comp (g := aff t₀ ρ π) hc.continuousOn hUV, fun z w hd => ?_⟩
  simp only [ha]
  exact h.2 _ _ fun ζ hζ => by rw [← ha]; exact hUV _ (hd ζ hζ)

theorem one_le_logSize {n : ℕ} (a : ℕ) (u : Fin n → ℂ) : 1 ≤ Flat.logSize a u :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem logSize_le {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {P : Ideal (MRing J)} {n a₀ : ℕ}
    {Bd : Set ((Σ k, J k) → ℂ)} (χ : SncChart P n Bd) (t₀ : Fin n → ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (π : Equiv.Perm (Fin n))
    (hu : ∀ u ∈ ball (0 : Fin n → ℂ) 1, aff t₀ ρ π u ∈ ball (0 : Fin n → ℂ) 1 ∧
      (χ.γ (aff t₀ ρ π u) ∉ Bd → u ∈ Flat.punct n a₀ 1)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ u ∈ Flat.punct n a₀ 1, 1 ≤ Real.log (χ.logR (aff t₀ ρ π u)) ∧
      1 + Real.log (Flat.logSize a₀ u) ≤ A * Real.log (χ.logR (aff t₀ ρ π u)) := by
  classical
  have hρ' : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hρ.ne'
  have hbr : ∀ i : Fin n, i.val < a₀ → (π.symm i).val < χ.a ∧ t₀ (π.symm i) = 0 := by
    intro i hi
    let u : Fin n → ℂ := fun k => if k = i then 0 else if t₀ (π.symm k) = 0 then 1 / 2 else 0
    have hu1 : u ∈ ball (0 : Fin n → ℂ) 1 := by
      rw [mem_ball_zero_iff, pi_norm_lt_iff one_pos]
      intro k
      simp only [u]
      split_ifs <;> norm_num
    have hb : χ.γ (aff t₀ ρ π u) ∈ Bd := by
      by_contra hn
      exact ((hu u hu1).2 hn).2 i hi (by simp [u])
    obtain ⟨j, hj, h0⟩ := (χ.boundary _ (hu u hu1).1).1 hb
    by_cases hji : π j = i
    · subst hji
      simp only [Equiv.symm_apply_apply]
      exact ⟨hj, by simpa [aff, u] using h0⟩
    · exfalso
      by_cases ht : t₀ j = 0 <;> simp [aff, u, hji, ht, hρ'] at h0
  set A₀ : ℝ := 1 + n * (1 + |Real.log ρ|) with hA₀
  have hA1 : 1 ≤ A₀ := le_add_of_nonneg_right (by positivity)
  refine ⟨2 + Real.log A₀, by linarith [Real.log_nonneg hA1], fun u hu' => ?_⟩
  set t := aff t₀ ρ π u with ht
  have ht1 : ∀ k, ‖t k‖ < 1 := (pi_norm_lt_iff one_pos).1 (mem_ball_zero_iff.1 (hu u hu'.1).1)
  have hu1 : ∀ k, ‖u k‖ < 1 := (pi_norm_lt_iff one_pos).1 (mem_ball_zero_iff.1 hu'.1)
  have hterm : ∀ i : Fin n, 0 ≤ if (i : ℕ) < χ.a then Real.log (1 / ‖t i‖ ^ 2) else 0 := by
    intro i
    split_ifs
    · rw [one_div, Real.log_inv, neg_nonneg]
      exact Real.log_nonpos (by positivity) (pow_le_one₀ (norm_nonneg _) (ht1 i).le)
    · exact le_rfl
  have he : Real.exp 1 ≤ χ.logR t := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hterm i)
  have he1 : 1 ≤ χ.logR t := (Real.one_le_exp zero_le_one).trans he
  have hl1 : 1 ≤ Real.log (χ.logR t) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact he
  have hone : ∀ i : Fin n, i.val < a₀ → |Real.log ‖u i‖| ≤ (1 + |Real.log ρ|) * χ.logR t := by
    intro i hi
    obtain ⟨h1, h2⟩ := hbr i hi
    have h3 : t (π.symm i) = ρ * u i := by simp [ht, aff, h2]
    have h4 : Real.log (1 / ‖t (π.symm i)‖ ^ 2) ≤ χ.logR t := by
      have := Finset.single_le_sum (fun i _ => hterm i) (Finset.mem_univ (π.symm i))
      rw [if_pos h1] at this
      exact this.trans (le_add_of_nonneg_left (Real.exp_pos 1).le)
    have h5 : 0 < ‖u i‖ := norm_pos_iff.2 (hu'.2 i hi)
    rw [h3, one_div, Real.log_inv, Real.log_pow, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ.le,
      Real.log_mul hρ.ne' h5.ne'] at h4
    rw [abs_of_neg (Real.log_neg h5 (hu1 i))]
    push_cast at h4
    nlinarith [le_abs_self (Real.log ρ), abs_nonneg (Real.log ρ)]
  have hsz : Flat.logSize a₀ u ≤ A₀ * χ.logR t := by
    have h1 := Finset.sum_le_card_nsmul (Finset.univ.filter fun i : Fin n => i.val < a₀)
      (fun i => |Real.log ‖u i‖|) _ fun i hi => hone i (Finset.mem_filter.1 hi).2
    have h2 : ((Finset.univ.filter fun i : Fin n => i.val < a₀).card : ℝ) ≤ n := by
      exact_mod_cast (Finset.card_le_univ _).trans (Fintype.card_fin n).le
    have h3 : 0 ≤ (1 + |Real.log ρ|) * χ.logR t := by positivity
    rw [nsmul_eq_mul] at h1
    unfold Flat.logSize
    nlinarith [mul_le_mul_of_nonneg_right h2 h3]
  have h6 := Real.log_le_log (by linarith [one_le_logSize a₀ u]) hsz
  rw [Real.log_mul (by linarith) (by linarith)] at h6
  exact ⟨hl1, by nlinarith [Real.log_nonneg hA1]⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {Xo : ∀ l : Tor.Level H, Moduli D l} {l : Tor.Level H} {c : Coeff l}
  {Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)} {II : IntersectionSystem} {K : Type} [Fintype K]
  {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : CMType H → Type}
  [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
  {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc} {S₀ : Finset ℕ}

theorem near_bdd (hG : Top.Given) (Or : CptOrigin Y S₀ Dc Hd) {U : ((Σ k, J k) → ℂ) → ℝ}
    (hU : Or.𝔐.IsCuspWeight Or.sm U) (hP : ChartPsh Dc (corrW Hd U)) (a : Fin Dc.nCharts)
    (t₀ : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) (ht₀ : t₀ ∈ ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1) :
    ∃ ε > (0 : ℝ), ∃ C : ℝ, ∀ t ∈ offBd Dc a, ‖t - t₀‖ < ε → |corrW Hd U ((Dc.chart a).γ t)| ≤ C ∧
      U ((Dc.chart a).γ t) ≤ C * Real.log ((Dc.chart a).logR t) ∧
      |phMu Hd ((Dc.chart a).γ t)| ≤ C * Real.log ((Dc.chart a).logR t) := by
  classical
  obtain ⟨a₀, g, Λ, i₁, i₂, L, π, ρ, r, σ, b, G, hρ, hr, hr1, hσ, hb, hGd, hu, hw⟩ :=
    chart_formula hG Or hU a t₀ ht₀
  have hm : 1 ≤ Dc.N - Dc.j := by
    have := Dc.j_le
    have := Dc.two_le_N
    omega
  obtain ⟨ρ₁, C₁, hρ₁, hul⟩ := GlobalTheory.T.riemann_form_lower_bound_near_cusp E _ a₀ g Λ (CMType H) L σ _ b hσ hm hb
  obtain ⟨δ₂, hδ₂, C₂, hlow⟩ := lower_centre L σ b hσ hm hb
  have hGc : ContinuousAt (fun u => |(G u).re|) 0 :=
    (Complex.continuous_re.continuousAt.comp (hGd.continuousOn.continuousAt (ball_mem_nhds _ hr))).abs
  obtain ⟨δ₃, hδ₃, hGb⟩ := Metric.eventually_nhds_iff_ball.1
    (hGc.eventually (gt_mem_nhds (lt_add_one |(G 0).re|)))
  set B := |(G 0).re| + 1 with hB
  have hB0 : 0 ≤ B := by positivity
  obtain ⟨A, hA, hsz⟩ := logSize_le (a₀ := a₀) (Dc.chart a) t₀ hρ π fun u hu' =>
    ⟨(hu u hu').1, fun h => (hu u hu').2.1 ⟨(hu u hu').1, h⟩⟩
  obtain ⟨δ, hδ, d1, d2, d3, d4⟩ : ∃ δ > (0 : ℝ), δ ≤ r ∧ δ ≤ ρ₁ ∧ δ ≤ δ₂ ∧ δ ≤ δ₃ :=
    ⟨min (min r ρ₁) (min δ₂ δ₃), lt_min (lt_min hr hρ₁) (lt_min hδ₂ hδ₃),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  have hsub : ∀ u ∈ Flat.punct (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) a₀ δ, u ∈ Flat.punct (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) a₀ 1 :=
    fun u h => ⟨ball_subset_ball (d1.trans hr1) h.1, h.2⟩
  have key : ∀ u ∈ Flat.punct (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) a₀ δ, ∃ ld cw gr ℓ : ℝ, ℓ = 1 + Real.log (Flat.logSize a₀ u) ∧ 1 ≤ ℓ ∧
      phMu Hd ((Dc.chart a).γ (aff t₀ ρ π u)) = gr + ld / 2 ∧ U ((Dc.chart a).γ (aff t₀ ρ π u)) = cw ∧
      cw ≤ |C₁| * ℓ ∧ |ld| ≤ |C₁| * ℓ ∧ -C₂ ≤ ld + cw ∧ |gr| ≤ B := by
    intro u hu'
    obtain ⟨w, hlw, rfl⟩ := exists_lift L.a_le (hsub u hu')
    have hn := mem_ball_zero_iff.1 hu'.1
    obtain ⟨e1, e2⟩ := hw w hlw (ball_subset_ball d1 hu'.1) (hsub _ hu')
    obtain ⟨-, b1, b2⟩ := hul w hlw (hn.trans_le d2)
    have hl : 1 ≤ 1 + Real.log (Flat.logSize a₀ (expCover a₀ w)) :=
      le_add_of_nonneg_right (Real.log_nonneg (one_le_logSize _ _))
    have hm' := mul_le_mul_of_nonneg_right (le_abs_self C₁) (zero_le_one.trans hl)
    exact ⟨_, _, _, _, rfl, hl, e1, e2, b1.trans hm', b2.trans hm', hlow w hlw (hn.trans_le d3),
      (hGb _ (ball_subset_ball d4 hu'.1)).le⟩
  have hps : IsPsh (Flat.punct (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) a₀ δ) fun u => corrW Hd U ((Dc.chart a).γ (aff t₀ ρ π u)) :=
    isPsh_comp_aff t₀ ρ π (hP a) fun u h => (hu u (hsub u h).1).2.2 (hsub u h)
  obtain ⟨C₃, hC₃⟩ := GlobalTheory.T.psh_log_growth_bounded_near_puncture _ a₀ δ (B + |C₁|) _ hδ (d1.trans hr1) hps fun u h => by
    obtain ⟨ld, cw, gr, ℓ, h0, h1, e1, e2, b1, b2, -, b4⟩ := key u h
    simp only [corrW, e1, e2, ← h0]
    nlinarith [(abs_le.1 b2).2, (abs_le.1 b4).2]
  have hc : Continuous (affInv t₀ ρ π) := by
    unfold affInv
    fun_prop
  have h00 : affInv t₀ ρ π t₀ = 0 := by
    funext i
    simp [affInv]
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 ((hc.tendsto t₀).eventually
    (by rw [h00]; exact ball_mem_nhds _ (half_pos hδ) : ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) (δ / 2) ∈ 𝓝 (affInv t₀ ρ π t₀)))
  refine ⟨ε, hε, |C₃| + |C₂| + B + |C₁| * A, fun t ht hε' => ?_⟩
  have hu2 := hball t (by rwa [mem_ball, dist_eq_norm])
  have hu3 : affInv t₀ ρ π t ∈ ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) δ := ball_subset_ball (half_le_self hδ.le) hu2
  have hat := aff_affInv t₀ hρ π t
  have hp1 := (hu _ (ball_subset_ball (d1.trans hr1) hu3)).2.1 (by rw [hat]; exact ht)
  obtain ⟨ld, cw, gr, ℓ, h0, h1, e1, e2, b1, b2, b3, b4⟩ := key _ ⟨hu3, hp1.2⟩
  have h3 := hC₃ _ ⟨hu2, hp1.2⟩
  obtain ⟨s1, s2⟩ := hsz _ hp1
  simp only [hat] at e1 e2 h3 s1 s2
  rw [← h0] at s2
  set R := Real.log ((Dc.chart a).logR t)
  have p1 := abs_nonneg C₁
  have p2 := abs_nonneg C₂
  have p3 := abs_nonneg C₃
  have q1 : |C₁| * ℓ ≤ |C₁| * A * R := by rw [_root_.mul_assoc]; exact mul_le_mul_of_nonneg_left s2 p1
  have q2 : 0 ≤ |C₁| * A := mul_nonneg p1 hA
  have q3 : B ≤ (|C₃| + |C₂| + B) * R := by nlinarith
  have q4 : 0 ≤ |C₁| * ℓ := by positivity
  refine ⟨abs_le.2 ⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [corrW, e1, e2]
    linarith [(abs_le.1 b4).1, le_abs_self C₂]
  · linarith [le_abs_self C₃]
  · rw [e2]
    linarith
  · rw [e1]
    refine abs_le.2 ⟨?_, ?_⟩
    · linarith [(abs_le.1 b4).1, (abs_le.1 b2).1]
    · linarith [(abs_le.1 b4).2, (abs_le.1 b2).2]

theorem corr_bdd : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (U : ((Σ k, J k) → ℂ) → ℝ), Or.𝔐.IsCuspWeight Or.sm U → ChartBdd Dc (corrW Hd U) ∧ ∀ a, ∀ t₀ ∈ Metric.ball (0 : Fin (Fintype.card (CMType H) * Dc.j * (Dc.N - Dc.j)) → ℂ) 1, ∃ ε > (0 : ℝ), ∃ C : ℝ, ∀ t ∈ offBd Dc a, ‖t - t₀‖ < ε → U ((Dc.chart a).γ t) ≤ C * Real.log ((Dc.chart a).logR t) ∧ |phMu Hd ((Dc.chart a).γ t)| ≤ C * Real.log ((Dc.chart a).logR t) := by
  intro hG E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or U hU
  have hP := (GlobalTheory.T.cusp_intersection_positive hG E H D Xo l c Y II K J Ω W Dc Hd S₀ Or U hU).2.2.1
  refine ⟨fun a t₀ ht₀ => ?_, fun a t₀ ht₀ => ?_⟩
  · obtain ⟨ε, hε, C, h⟩ := near_bdd hG Or hU hP a t₀ ht₀
    exact ⟨ε, hε, C, fun t ht h' => (h t ht h').1⟩
  · obtain ⟨ε, hε, C, h⟩ := near_bdd hG Or hU hP a t₀ ht₀
    exact ⟨ε, hε, C, fun t ht h' => (h t ht h').2⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.CorrBdd
