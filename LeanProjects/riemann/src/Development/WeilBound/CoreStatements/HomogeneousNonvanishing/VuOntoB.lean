import Development.WeilBound.CoreStatements.ProjectiveValuations.FrequentlyNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenframeSpecializationUniformBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormFactorInvLePowHolomorphicOrbitPeriodBoundStatement

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.OntoDef GlobalTheory.CompHS
open GlobalTheory.CompanionTheory.Ar.HolExt DifferentiableLines

noncomputable section

namespace PositivityTheory.UnitarySelfGeneration.VuOnto

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {r : ℕ} {σ : c.F →+* ℂ}

section ThetaShiftProofs

open Limits GlobalTheory.CxPts Filter Topology GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 800000 in

theorem tendsto_arc_readsZ {V : Unf Xo c σ r} (hσ : GoodEmb c σ) (hU : IsUnf V) (T : TorFlag Xo c)
    {ee : Ix D → ℤ} (hee : ee none = 0) {k : V.Comp} {la : ReciprocityTheory.ChartRestriction.G.FD.Wt (V.X k).Ψ r}
    {P : Frame (V.X k).Ψ r → ℂ} (hP : P ∈ (V.X k).SS la)
    {h : (T.X.LL ee).ι → GlobalTheory.CxPts (flagStr T.X) σ → ℂ}
    (hR : Reads V T ee k P h) (hZ : OffZero V T k h) (i : T.X.F.J)
    {W : T.X.YY.Opens} (hW : IsAffineOpen W) [IsDomain Γ(T.X.YY, W)] (hWi : W ≤ T.X.F.U i)
    (s : ℂ → GlobalTheory.CxPts (flagStr T.X) σ) {ρ : ℝ} (hρ : 0 < ρ) (hsW : ∀ u ∈ Metric.ball (0 : ℂ) ρ, s u ∈ ptsIn _ σ W)
    (hsd : ∀ f : Γ(T.X.YY, W), DifferentiableOn ℂ (fun u => ev _ σ W f (s u)) (Metric.ball 0 ρ))
    (h0 : s 0 ∉ ptsIn _ σ (flagOpen T.X)) (h1 : ∀ u ∈ Metric.ball (0 : ℂ) ρ, u ≠ 0 → s u ∈ ptsIn _ σ (flagOpen T.X)) :
    Tendsto (fun u => h i (s u)) (𝓝[≠] 0) (𝓝 0) := by
  classical
  obtain ⟨-, g1, g2, -⟩ := GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H D l Xo c (CAt σ)
  let A : Type := Γ(T.X.YY, W)
  let q : Sp A ⟶ T.X.YY := GlobalTheory.FlagMod.tau hW
  let φ : c.F →+* A := (GlobalTheory.FlagMod.ev (q ≫ flagStr T.X) ⊤ le_top).comp (toΓ c.F)
  have hφ : q ≫ flagStr T.X = spMap φ := (GlobalTheory.FlagMod.spMap_ev_top _).symm
  have hz : ⊤ ≤ q ⁻¹ᵁ T.X.F.U i := GlobalTheory.FlagMod.tau_le hW hWi
  have hxc : (q ≫ T.X.π) ≫ T.Y.s = spMap φ ≫ spMap (RingHom.id c.F) :=
    ((Category.assoc _ _ _).trans hφ).trans ((Category.comp_id _).symm.trans (congrArg (_ ≫ ·) (Spec.map_id _).symm))
  let x : Sp A ⟶ gen T.Y := pullback.lift _ _ hxc
  have hx : q ≫ T.X.π = x ≫ genι T.Y := (pullback.lift_fst _ _ _).symm
  have hxs : x ≫ genStr T.Y = spMap φ := pullback.lift_snd _ _ _
  obtain ⟨fr, hfr⟩ := exists_eigFrame_tau T hW hφ i hz hx
  have hb0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ := Metric.mem_ball_self hρ
  let ψ : ℂ → (A →+* ℂ) := fun u => if hu : u ∈ Metric.ball (0 : ℂ) ρ then
    GlobalTheory.FlagMod.ev (s u).1 W (hsW u hu) else GlobalTheory.FlagMod.ev (s 0).1 W (hsW 0 hb0)
  have hψ : ∀ u (hu : u ∈ Metric.ball (0 : ℂ) ρ), ψ u = GlobalTheory.FlagMod.ev (s u).1 W (hsW u hu) := fun u hu => dif_pos hu
  have hψq : ∀ u ∈ Metric.ball (0 : ℂ) ρ, spMap (ψ u) ≫ q = (s u).1 := fun u hu => by
    rw [hψ u hu]
    exact GlobalTheory.FlagMod.spMap_ev (s u).1 hW _
  have hφu : ∀ u ∈ Metric.ball (0 : ℂ) ρ, (ψ u).comp φ = σ := fun u hu => by
    have e₁ : spMap ((ψ u).comp φ) = spMap (ψ u) ≫ spMap φ := Spec.map_comp _ _
    rw [← hφ, ← Category.assoc, hψq u hu, (s u).2] at e₁
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e₁)
  have key : ∀ u ∈ Metric.ball (0 : ℂ) ρ, ∀ p : Sp ℂ,
      (s u).1 p ∈ flagOpen T.X ↔ (spMap (ψ u) ≫ x) p ∉ genBd T.Y := by
    intro u hu p
    have := GlobalTheory.LogKS.isIso_fst T.Y
    have e : (s u).1 p ∈ flagOpen T.X ↔ genι T.Y ((spMap (ψ u) ≫ x) p) ∈ Set.range T.Y.j := by
      rw [← Scheme.Hom.comp_apply, Category.assoc, ← hx, ← Category.assoc, hψq u hu]
      exact Iff.rfl
    rw [e, mem_genBd, not_not]
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, (genι T.Y).isOpenEmbedding.injective (by rw [← ha]; rfl)⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, by rw [← ha]; rfl⟩
  have hb : IsBdArc T.Y σ φ x ψ ρ := by
    refine ⟨⟨⟨hρ, fun f => (hsd f).congr fun u hu => ?_⟩, hxs, hφu⟩, fun p => ?_,
      fun u hu hne p => (key u hu p).1 (h1 u hu hne (Set.mem_univ p))⟩
    · rw [hψ u hu]
      exact (ev_eq (hsW u hu) f).symm
    · by_contra hp
      refine h0 (mem_ptsIn.2 ?_)
      rw [Subsingleton.elim (α := PrimeSpectrum ℂ) (IsLocalRing.closedPoint ℂ) p]
      exact (key 0 hb0 p).2 hp
  have hy' : ∀ u : ℂ, u ∈ Metric.ball (0 : ℂ) ρ ∧ u ≠ 0 → ∃ y : FrPt Xo c (CAt σ), Matches fr (ψ u) y :=
    fun u hu => GlobalTheory.ShFam.BdArc.exists_matches E H D l Xo c c.F (RingHom.id c.F) T.Y σ _ φ x fr (ψ u) hxs
      (hφu u hu.1) (hb.2.2 u hu.1 hu.2)
  have hr : ((ρ / 2 : ℝ) : ℂ) ∈ Metric.ball (0 : ℂ) ρ ∧ ((ρ / 2 : ℝ) : ℂ) ≠ 0 := by
    refine ⟨?_, by exact_mod_cast (half_pos hρ).ne'⟩
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_of_nonneg (half_pos hρ).le]
    exact half_lt_self hρ
  have : Nonempty (FrPt Xo c (CAt σ)) := ⟨(hy' _ hr).choose⟩
  choose! y hy using hy'
  have hm : ∀ u ∈ Metric.ball (0 : ℂ) ρ, u ≠ 0 → Matches fr (ψ u) (y u) := fun u hu hne => hy u ⟨hu, hne⟩
  obtain ⟨k', T₀, M₀, γ₀, xx, hT, hO₀, hL⟩ :=
    GlobalTheory.T.exists_holomorphicFrameOrbit_lift_of_arc E H D l Xo c _ _ T.Y σ r V A φ x fr ψ ρ y hσ hU hb.1 hm
  have hne0 : ∀ w, eTwoPi w ≠ 0 := fun w => Complex.exp_ne_zero _
  have hi : ∀ u ∈ Metric.ball (0 : ℂ) ρ, ⊤ ≤ zOf (s u) ⁻¹ᵁ T.X.F.U i := fun u hu => ptsIn_mono hWi (hsW u hu)
  have hfb : ∀ w (hw : T₀ < w.im), ∃ (hd : xx w ∈ (V.X k').dom) (Q : FrPt Xo c (CAt σ)) (t : Ix D → (CAt σ)ˣ),
      T.X.F.ChartFr i (zOf (s (eTwoPi w))) (hi _ (hT w hw)) Q ∧ FrBor t Q (V.un k' ⟨_, hd⟩) ∧ ∀ s, t (some s) = 1 := by
    intro w hw
    obtain ⟨hd, hl⟩ := hL w hw
    exact ⟨hd, exists_frBor_of_matches T q i hz hx fr hfr (ψ _)
      (matches_of_sameLie (hm _ (hT w hw) (hne0 w)) hl) (hψq _ (hT w hw)) _⟩
  have hev : ∀ᶠ w in imTop, T₀ < w.im := (tendsto_comap (f := Complex.im)).eventually (eventually_gt_atTop _)
  refine tendsto_punctured ?_
  by_cases hk : k' = k
  swap
  · refine tendsto_const_nhds.congr' (hev.mono fun w hw => (hZ i _ fun x' hx' e => hk ?_).symm)
    obtain ⟨hd, Q, t, hQ, ht, -⟩ := hfb w hw
    have e' : T.X.ptY (V.un k ⟨x', hx'⟩) = zOf (s (eTwoPi w)) := e
    have hlx : T.X.F.Lies (zOf (s (eTwoPi w))) (V.un k ⟨x', hx'⟩) := e' ▸ T.X.lies_ptY _
    obtain ⟨t', ht'⟩ := hQ.exists_frBor hlx
    obtain ⟨γ, -, β, -, h'⟩ := (hU.2.2.2.1 k' k _ _).1 ⟨_, g1 _ _ _ _ _ (g2 _ _ _ ht) ht'⟩
    exact (Sigma.mk.inj h').1.symm
  subst hk
  obtain ⟨M, γ, hO, hγ⟩ := GlobalTheory.T.exists_holomorphicFrameOrbit_unipotent_order_two E r _ T₀ M₀ γ₀ xx hO₀
  have hne : γ ≠ 1 := by
    rintro rfl
    obtain ⟨x₀, hx₀, x', a1, a2⟩ := GlobalTheory.T.trivial_monodromy_orbit_converges_symmetric_domain E r _ T₀ M xx hO
    exact GlobalTheory.T.boundary_arc_lift_not_converges_symmetric_domain E H D l Xo c _ _ T.Y σ r V A φ x fr ψ ρ y k' T₀ xx hσ hU hb hm hL x₀ hx₀ x' a1 a2
  obtain ⟨ξ, c', hξ, hc', ht⟩ := GlobalTheory.T.holomorphicFrameOrbit_isotropic_vector_short E r _ T₀ M γ xx hO hγ hne
  obtain ⟨m, v, Lp, Lm, hlim⟩ := GlobalTheory.T.exists_arcLift_periods_tendsto_span E H D l Xo c _ _ T.Y σ r V A φ x fr ψ ρ y k' T₀ M γ xx hσ hU hb.1 hm hO hL
  have hper := GlobalTheory.T.eigenframe_specialization_uniform_bound E H D l Xo c _ _ T.Y σ r V A φ x fr ψ ρ y k' T₀ M γ xx hσ hU hb.1 hm hO hL
  obtain ⟨C', B, hn⟩ := GlobalTheory.T.normFactor_inv_le_pow_holomorphicOrbit_periodBound E r _ T₀ M γ xx la m v Lp Lm hO hlim hper
  have hp := tendsto_cusp hP hO.2.2.2.1 hξ hc' ht hn
  refine hp.congr' ?_
  filter_upwards [hev] with w hw
  obtain ⟨hd, Q, t, hQ, ht, ht1⟩ := hfb w hw
  have hu := hT w hw
  have e₁ : P (xx w) = chr ee t * h i (s (eTwoPi w)) :=
    hR (xx w) hd i _ (hi _ hu) Q t (GlobalTheory.FlagMod.FlagCover.eq_ptY (hQ.lies.frBor ht)).symm hQ ht
  rw [chr_of_some ht1, hee, zpow_zero, one_mul] at e₁
  exact e₁

end ThetaShiftProofs

open GlobalTheory.CxPts Filter Topology ReciprocityTheory.ChartRestriction.G.DVR.FlatBC

set_option maxHeartbeats 800000 in

theorem holoOn_bdZ {V : Unf Xo c σ r} (hσ : GoodEmb c σ) (hU : IsUnf V) (T : TorFlag Xo c)
    {ee : Ix D → ℤ} (hee : ee none = 0) {k : V.Comp} {la : ReciprocityTheory.ChartRestriction.G.FD.Wt (V.X k).Ψ r}
    {P : Frame (V.X k).Ψ r → ℂ} (hP : P ∈ (V.X k).SS la) {d : ℕ} [SmoothOfRelativeDimension d (flagStr T.X)]
    (R : GlobalTheory.AnRead (flagStr T.X) σ d)
    {h : (T.X.LL ee).ι → GlobalTheory.CxPts (flagStr T.X) σ → ℂ}
    (hR : Reads V T ee k P h) (hZ : OffZero V T k h)
    (hh : ∀ i, R.HoloOn (ptsIn _ σ ((T.X.LL ee).U i) ∩ ptsIn _ σ (flagOpen T.X)) (h i))
    (i : T.X.F.J) :
    R.HoloOn (ptsIn _ σ (T.X.F.U i)) (h i) := by
  intro j v hv
  have hs : Smooth (flagStr T.X) := SmoothOfRelativeDimension.smooth d _
  obtain ⟨-, hn, hl⟩ := GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field c.F _ _ hs
  have := GlobalTheory.IsNormalScheme.of_pred hn
  let C := R.chart j
  let L := EuclideanSpace.equiv (Fin d) ℂ
  let y₀ := C.e.symm v
  obtain ⟨W₁, hyW₁, hW₁⟩ := GlobalTheory.ModelChart.exists_open_isDomain T.X.YY (y₀.1 (IsLocalRing.closedPoint ℂ))
  obtain ⟨W, hW, hyW, hWle⟩ := GlobalTheory.Points.exists_isAffineOpen_le y₀.1
    (mem_ptsIn_inf.2 ⟨mem_ptsIn.2 hyW₁, hv.2⟩ : y₀ ∈ ptsIn _ σ (W₁ ⊓ T.X.F.U i))
  have hyW' : y₀ ∈ ptsIn _ σ W := hyW
  have := hW₁ W (mem_ptsIn.1 hyW') (hWle.trans inf_le_left)
  have hWi := hWle.trans inf_le_right
  obtain ⟨p, hpW, hpO⟩ := (dense_flagOpen T.X).inter_open_nonempty W W.isOpen ⟨_, mem_ptsIn.1 hyW'⟩
  obtain ⟨g, hgO, hpg⟩ := hW.exists_basicOpen_le (V := flagOpen T.X) ⟨p, hpO⟩ hpW
  have hg : g ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hpg
    exact hpg
  let s : (Fin d → ℂ) → GlobalTheory.CxPts (flagStr T.X) σ := fun b => C.e.symm (L.symm b)
  have ho : ∀ {S}, IsOpen S → IsOpen (L.symm ⁻¹' (C.e.target ∩ C.e.symm ⁻¹' S)) := fun hS =>
    (GlobalTheory.ChartGlue.isOpen_over C.e hS).preimage L.symm.continuous
  have hU' := ho (isOpen_ptsIn W)
  have hd : ∀ f : Γ(T.X.YY, W), DifferentiableOn ℂ (fun b => ev _ σ W f (s b))
      (L.symm ⁻¹' (C.e.target ∩ C.e.symm ⁻¹' ptsIn _ σ W)) := fun f =>
    (C.holo W f).comp L.symm.differentiableOn fun _ hb => hb
  have key : DifferentiableAt ℂ (fun b => h i (s b)) (L v) := by
    refine differentiableAt_of_lines hU' (ho ((isOpen_ptsIn (T.X.F.U i)).inter (isOpen_ptsIn (flagOpen T.X)))) (hd g)
      (fun t ht h0 => ⟨ht.1, ptsIn_mono hWi ht.2, ptsIn_mono hgO ((mem_ptsIn_basicOpen ht.2 g).2 h0)⟩)
      ((hh i j).comp L.symm.differentiableOn fun _ hb => hb) (fun τ hτ hτO w hw => ?_)
      (by simpa using ⟨hv.1, hyW'⟩) fun ρ hρ => ?_
    · have hout : s τ ∉ ptsIn _ σ (flagOpen T.X) := fun h' => hτO ⟨hτ.1, ptsIn_mono hWi hτ.2, h'⟩
      have h0 : h i (s τ) = 0 := hZ i _ fun x hx e => hout (mem_open_of_ptY T _ _ e)
      have hline : Differentiable ℂ fun z : ℂ => τ + z • w := by fun_prop
      have hnb : ∀ᶠ z : ℂ in 𝓝 0, τ + z • w ∈ L.symm ⁻¹' (C.e.target ∩ C.e.symm ⁻¹' ptsIn _ σ W) :=
        hline.continuous.continuousAt.preimage_mem_nhds (hU'.mem_nhds (by simpa using hτ))
      obtain ⟨ρ, hρ, hb⟩ := Metric.eventually_nhds_iff_ball.1 (hnb.and (eventually_nhdsWithin_iff.1 hw))
      show Tendsto (fun z : ℂ => h i (s (τ + z • w))) _ (𝓝 (h i (s τ)))
      rw [h0]
      have b₁ : ∀ u ∈ Metric.ball (0 : ℂ) ρ, s (τ + u • w) ∈ ptsIn _ σ W := fun u hu => (hb u hu).1.2
      have b₂ : ∀ f : Γ(T.X.YY, W), DifferentiableOn ℂ (fun u : ℂ => ev _ σ W f (s (τ + u • w))) (Metric.ball 0 ρ) :=
        fun f => DifferentiableOn.comp (g := fun b => ev _ σ W f (s b)) (f := fun u : ℂ => τ + u • w) (hd f)
          hline.differentiableOn fun u hu => (hb u hu).1
      have b₃ : s (τ + (0 : ℂ) • w) ∉ ptsIn _ σ (flagOpen T.X) := by
        rw [zero_smul, add_zero]
        exact hout
      have b₄ : ∀ u ∈ Metric.ball (0 : ℂ) ρ, u ≠ 0 → s (τ + u • w) ∈ ptsIn _ σ (flagOpen T.X) :=
        fun u hu hu0 => ((hb u hu).2 hu0).2.2
      exact tendsto_arc_readsZ hσ hU T hee hP hR hZ i hW hWi (fun z => s (τ + z • w)) hρ b₁ b₂ b₃ b₄
    · have hsrc : y₀ ∈ C.e.source := C.e.map_target hv.1
      have hc : ContinuousAt (fun y => L (C.e y)) y₀ := L.continuous.continuousAt.comp (C.e.continuousAt hsrc)
      have hN : {y | L (C.e y) ∈ Metric.ball (L v) ρ} ∈ 𝓝 y₀ :=
        hc.preimage_mem_nhds (by rw [C.e.right_inv hv.1]; exact Metric.ball_mem_nhds _ hρ)
      obtain ⟨y', hy', hne⟩ := frequently_ne_zero (flagStr T.X) hW hg hyW'
        (inter_mem hN (C.e.open_source.mem_nhds hsrc))
      refine ⟨_, hy'.1, ?_⟩
      simp only [s, ContinuousLinearEquiv.symm_apply_apply]
      rwa [C.e.left_inv hy'.2]
  refine DifferentiableAt.differentiableWithinAt ?_
  refine (key.comp v L.differentiableAt).congr_of_eventuallyEq (Eventually.of_forall fun w => ?_)
  simp only [s, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  rfl

end PositivityTheory.UnitarySelfGeneration.VuOnto
