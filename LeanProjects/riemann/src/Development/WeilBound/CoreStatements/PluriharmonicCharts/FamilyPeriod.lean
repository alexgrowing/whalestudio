import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG
import Development.WeilBound.CoreStatements.PluriharmonicCharts.IsDerivAt0Congr
import Development.WeilBound.CoreStatements.PluriharmonicCharts.DerivZero
import Development.WeilBound.CoreStatements.PluriharmonicCharts.XCBmExistsSumframe
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.InteriorPointPolarisedStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PairSumFrameAtPointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixChangeFrameStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

set_option linter.unusedSectionVars false

namespace PositivityTheory.Xgp.c_bm_exists_period

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem emb_ext {σ σ' : E →+* ℂ} (h : ∀ t : 𝓞 E, σ t = σ' t) : σ = σ' :=
  IsFractionRing.ringHom_ext (A := 𝓞 E) h

variable {Xo : ∀ l : Level H, Moduli D l} {l : Level H} {c : Coeff l} {Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)}
  {S : Finset ℕ} {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ]
  {y : (Σ k, ι k) → Φ} {M : FlagModel y (CMType H) (D.p + D.q) D.p} {𝔐 : HodgeCpt Y S M.x}

theorem family_period (hN : N1c) (tie : FlagTie M 𝔐) (hpq : 1 ≤ D.p + D.q)
    {F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk} (hF : M.IsFrame F) {n : ℕ}
    (p : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X)) (τ₀ : c.F →+* ℂ)
    (hτ : (τ₀.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0)
    (hp : IsHolTo (Metric.ball 0 1) p)
    (hc : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, p u ≫ 𝔐.f ≫ Y.s = spMap (τ₀.comp (algebraMap (𝓞 c.F) c.F)))
    (hi : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, 𝔐.Interior (p u))
    (hg : M.GoodAt F (ptIdeal 𝔐.ξ M.x ⟨centre (p 0), 𝔐.all _⟩)) :
    ∃ (ρ : ℝ) (B' : Set (Fin n → ℂ)) (Pi Γ : CMType H → (Fin n → ℂ) → Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ),
      0 < ρ ∧ ρ ≤ 1 ∧ IsOpen B' ∧ 0 ∈ B' ∧ B' ⊆ Metric.ball 0 1 ∧ (∀ τ, HolM B' (Pi τ)) ∧
      (∀ τ, ∀ u ∈ B', 𝔐.M.GramAt 𝔐.t.PP.L (p ((ρ : ℂ) • u)) (gb tie F τ) (Γ τ u) ∧
        IsPeriodGram D.p (Pi τ u) (blockG (Γ τ u))) ∧
      ∀ v, (∀ τ (a b : Fin (D.p + D.q)), D.p + D.q - D.p ≤ (a : ℕ) → (b : ℕ) < D.p + D.q - D.p →
          ((Pi τ 0)⁻¹ * dM (Pi τ) 0 v) a b = 0) →
        ∃ V : Sp (DualNumber ℂ) ⟶ 𝔐.X, IsDerivAt0 (fun u => p ((ρ : ℂ) • u)) v V ∧
          V ≫ 𝔐.f = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ p 0 ≫ 𝔐.f := by
  classical
  obtain ⟨g, ty, hty⟩ := GlobalTheory.AllClasses.exists_isTypeFn H D.p D.q
  obtain ⟨FU⟩ := hN E H D l (Xo l) _ g ty hpq hτ hty
  have hfr := fun τ => PositivityTheory.Xgp.isFrameAt_comap_gbS E H D Xo l c Y S K ι Φ y M 𝔐 tie F hF τ _ hg
  obtain ⟨i, ρ, B, P, W, G, hρ, hρ', hB, h0, hsub, hP, hW, hall, hder⟩ := model_periods 𝔐
    (fun a : CMType H × Fin (D.p + D.q) => gb tie F a.1 a.2) p τ₀ FU hp hc hi
    (fun a => GlobalTheory.T.hodge_generated_sum_specialization E H D l (Xo l) c Y S M.Ω _ _ M.x 𝔐 _ _ _ (gbS tie F a.1) (p 0) (𝔐.all _) (hfr a.1) a.2)
  let s : CMType H → (E →+* ℂ) := fun τ => τ₀.comp (τ.1.codRestrict c.F (c.conj τ.1))
  have hs : ∀ τ, s τ (H.rt : E) = H.rt0 := fun τ => by
    rw [← hτ]
    exact congrArg τ₀ (Subtype.ext τ.2)
  let Γ : CMType H → (Fin n → ℂ) → Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ := fun τ u =>
    Matrix.of fun i j => (Real.pi : ℂ) * hermForm (G u) (W (τ, j) u) (W (τ, i) u)
  have hΓ : ∀ τ, ∀ u ∈ B, 𝔐.M.GramAt 𝔐.t.PP.L (p ((ρ : ℂ) • u)) (gb tie F τ) (Γ τ u) := fun τ u hu =>
    (hall u hu).2.1 _ fun k => (τ, k)
  have hb0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  have hpos : ∀ τ, (Γ τ 0).PosDef := fun τ => by
    have hpol := GlobalTheory.T.interior_point_polarised E H D l (Xo l) c Y S M.Ω _ _ M.x 𝔐 _ (hi 0 hb0)
    obtain ⟨Γ', h1, h2⟩ := GlobalTheory.T.pair_sum_frame_at_point E H D l (Xo l) c Y S M.Ω _ _ M.x 𝔐 (.inl τ) (.inr τ) (D.p + D.q)
      (gbS tie F τ) _ (𝔐.all _) hpol (hfr τ)
    have h3 := hΓ τ 0 h0
    rw [smul_zero] at h3
    rw [GlobalTheory.T.gram_matrix_change_frame E H D l (Xo l) c Y S M.Ω _ _ M.x 𝔐 _ _ _ _ _ hpol h3 h1]
    exact h2
  have key := fun τ => exists_period_of_frames hty hB h0 hP (hs τ) (W := fun k => W (τ, k)) (fun k => hW _)
    (fun u hu a j hj => by
      by_contra hne
      refine hj (emb_ext fun t => ?_)
      have hm : gb tie F τ (omEmb D.p D.q a) ∈ 𝔐.Vgen (.inr τ) := by
        simp only [gb, gbS, ← blockEquiv_inl, Equiv.symm_apply_apply, Sum.elim_inl]
        exact (dualFam tie F τ a).2
      rw [mul_right_cancel₀ hne ((hall u hu).2.2 (τ, omEmb D.p D.q a) _ hm t j)]
      show s τ ((H.bar t : 𝓞 E) : E) = _
      rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]
      rfl)
    (fun u hu a j hj => by
      by_contra hne
      refine hj (emb_ext fun t => ?_)
      have hm : gb tie F τ (wEmb D.p D.q a) ∈ 𝔐.Vgen (.inl τ) := by
        simp only [gb, gbS, ← blockEquiv_inr, Equiv.symm_apply_apply, Sum.elim_inr]
        exact wFrame_mem tie F τ a
      exact mul_right_cancel₀ hne ((hall u hu).2.2 (τ, wEmb D.p D.q a) _ hm t j))
    (fun u hu => (hall u hu).1) (Γ := Γ τ) (fun u _ => rfl) (hpos τ)
  choose B' Pi hB' h0' hsub' hPi hgr hd using key
  refine ⟨ρ, B ∩ ⋂ τ, B' τ, Pi, Γ, hρ, hρ', hB.inter (isOpen_iInter_of_finite hB'), ⟨h0, Set.mem_iInter.2 h0'⟩,
    fun u hu => hsub hu.1, fun τ => (hPi τ).mono fun u hu => Set.mem_iInter.1 hu.2 τ,
    fun τ u hu => ⟨hΓ τ u hu.1, hgr τ u (Set.mem_iInter.1 hu.2 τ)⟩, fun v hv => hder v ?_⟩
  obtain ⟨α, β, h1, h2, h3, h4⟩ := deriv_zero FU i hB h0 hP v
  refine fun U f hU => h4 (fun j k hj => ?_) U f hU
  have hinj : Function.Injective fun τ : CMType H => (⟨s τ, hs τ⟩ : CMType H) := fun τ τ' e =>
    Subtype.ext (RingHom.ext fun a => congrArg Subtype.val
      (τ₀.injective (DFunLike.congr_fun (congrArg Subtype.val e) a)))
  obtain ⟨τ, hτ'⟩ := Finite.surjective_of_injective hinj ⟨ty j, hj⟩
  exact hd τ v (hv τ) α β h1 h2 h3 j k (congrArg Subtype.val hτ').symm

theorem gramFn_eq {r : ℕ} {b : Fin r → 𝔐.Li} {z : Sp ℂ ⟶ 𝔐.X} {w : (Σ k, baseIdx ι M.blk k) → ℂ}
    {Γ : Matrix (Fin r) (Fin r) ℂ} (hw : CoordsAt 𝔐.ξ M.x z w) (hi : 𝔐.Interior z)
    (h1 : 𝔐.M.GramAt 𝔐.t.PP.L z b Γ) : HodgeMetric.gramFn 𝔐 b w = Γ := by
  have tp := GlobalTheory.T.local_ring_points_existsUnique 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie ℂ
  have hex : ∃ (Γ : Matrix (Fin r) (Fin r) ℂ) (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X),
      CoordsAt 𝔐.ξ M.x z w ∧ 𝔐.Interior z ∧ 𝔐.M.GramAt 𝔐.t.PP.L z b Γ := ⟨Γ, z, hw, hi, h1⟩
  unfold HodgeMetric.gramFn
  rw [dif_pos hex]
  obtain ⟨z₀, hw₀, -, hΓ₀⟩ := hex.choose_spec
  have hz : z₀ = z := (tp.1 w hw.1 (tp.2.2 z w (𝔐.all _) hw).1).unique ⟨𝔐.all _, hw₀⟩ ⟨𝔐.all _, hw⟩
  rw [hz] at hΓ₀
  exact GlobalTheory.T.gram_matrix_change_frame E H D l (Xo l) c Y S M.Ω _ _ M.x 𝔐 z _ _ _ _
    (GlobalTheory.T.interior_point_polarised E H D l (Xo l) c Y S M.Ω _ _ M.x 𝔐 z hi) hΓ₀ h1

theorem exists_family {n : ℕ} (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) {Z : Set Rb.X} (hZ : IsClosed Z) {x : Rb.X}
    (hx : x ∉ Z) : ∃ (j : Fin Rb.A.n) (r : ℝ) (p : (Fin n → ℂ) → (Sp ℂ ⟶ 𝔐.X)), 0 < r ∧ x ∈ (Rb.A.chart j).source ∧
      DifferentiableOn ℂ (fun u => Rb.lift x ((Rb.A.chart j).symm (Rb.A.chart j x + (r : ℂ) • u))) (Metric.ball 0 1) ∧
      ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, (Rb.A.chart j).symm (Rb.A.chart j x + (r : ℂ) • u) ∉ Z ∧
        CoordsAt 𝔐.ξ M.x (p u) (Rb.lift x ((Rb.A.chart j).symm (Rb.A.chart j x + (r : ℂ) • u))) ∧
        CoordsAt 𝔐.ξ M.x (p u) (Rb.lift ((Rb.A.chart j).symm (Rb.A.chart j x + (r : ℂ) • u))
          ((Rb.A.chart j).symm (Rb.A.chart j x + (r : ℂ) • u))) := by
  obtain ⟨j, hj⟩ := Rb.A.cover x
  have ho : IsOpen ((Rb.A.chart j).target ∩ (Rb.A.chart j).symm ⁻¹' (Rb.U x ∩ Zᶜ)) :=
    (Rb.A.chart j).isOpen_inter_preimage_symm ((Rb.isOpen_U x).inter hZ.isOpen_compl)
  obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.1 ho (Rb.A.chart j x) ⟨(Rb.A.chart j).map_source hj, by
    rw [Set.mem_preimage, (Rb.A.chart j).left_inv hj]; exact ⟨Rb.mem_U x, hx⟩⟩
  have hm : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, Rb.A.chart j x + (r : ℂ) • u ∈
      (Rb.A.chart j).target ∩ (Rb.A.chart j).symm ⁻¹' (Rb.U x ∩ Zᶜ) := fun u hu => hb (by
    rw [mem_ball_zero_iff] at hu
    rw [mem_ball_iff_norm, add_sub_cancel_left, norm_smul, Complex.norm_real, Real.norm_of_nonneg hr.le]
    nlinarith)
  have hex : ∀ u ∈ Metric.ball (0 : Fin n → ℂ) 1, ∃ z : Sp ℂ ⟶ 𝔐.X, genPt 𝔐.ξ ⤳ centre z ∧
      CoordsAt 𝔐.ξ M.x z (Rb.lift x ((Rb.A.chart j).symm (Rb.A.chart j x + (r : ℂ) • u))) := fun u hu =>
    (GlobalTheory.T.complex_points_iff_centres 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie _).1 (Rb.mem x _ (hm u hu).2.1)
  haveI : Nonempty (Sp ℂ ⟶ 𝔐.X) := ⟨(hex 0 (by simp)).choose⟩
  choose! p hp₀ hp using hex
  refine ⟨j, r, p, hr, hj, differentiableOn_pi.2 fun q u hu => ?_, fun u hu => ⟨(hm u hu).2.2, hp u hu, ?_⟩⟩
  · have h1 := (Rb.holo x q j _ ⟨(hm u hu).1, (hm u hu).2.1⟩).differentiableAt
    have h2 : DifferentiableAt ℂ (fun u : Fin n → ℂ => Rb.A.chart j x + (r : ℂ) • u) u := by fun_prop
    exact (h1.comp u h2).differentiableWithinAt
  · obtain ⟨a, ha, e⟩ := Rb.compat _ x _ ⟨Rb.mem_U _, (hm u hu).2.1⟩
    exact (((GlobalTheory.T.local_ring_points_existsUnique 𝔐.X M.Ω 𝔐.ξ _ _ M.x 𝔐.tie ℂ).2.2 _ _ (𝔐.all _) (hp u hu)).2 _).2
      ⟨fun k => Units.mk0 (a k) (ha k), e⟩

theorem to_manifold {n : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas n X) (j : Fin A.n) {x : X}
    (hx : x ∈ (A.chart j).source) {r : ℂ} {B : Set (Fin n → ℂ)} (hB : IsOpen B) (h0 : 0 ∈ B) :
    IsOpen ((A.chart j).source ∩ (fun x' => r⁻¹ • (A.chart j x' - A.chart j x)) ⁻¹' B) ∧
    x ∈ ((A.chart j).source ∩ (fun x' => r⁻¹ • (A.chart j x' - A.chart j x)) ⁻¹' B) ∧
    ∀ f : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ f B →
      A.HoloOn ((A.chart j).source ∩ (fun x' => r⁻¹ • (A.chart j x' - A.chart j x)) ⁻¹' B)
        fun x' => f (r⁻¹ • (A.chart j x' - A.chart j x)) := by
  have hcont : ContinuousOn (fun x' => r⁻¹ • (A.chart j x' - A.chart j x)) (A.chart j).source :=
    ((A.chart j).continuousOn.sub continuousOn_const).const_smul r⁻¹
  refine ⟨hcont.isOpen_inter_preimage (A.chart j).open_source hB, ⟨hx, by simpa using h0⟩, fun f hf k t ht => ?_⟩
  have h1 : AnalyticAt ℂ (fun t => r⁻¹ • (A.chart j ((A.chart k).symm t) - A.chart j x)) t := by
    have := ((A.holo k j t ⟨ht.1, ht.2.1⟩).sub (analyticAt_const (v := A.chart j x))).const_smul (c := r⁻¹)
    exact this
  exact (GlobalTheory.SCV.analyticOnNhd_of_differentiableOn hB hf _ ht.2.2).comp_of_eq' h1 rfl

end PositivityTheory.Xgp.c_bm_exists_period
