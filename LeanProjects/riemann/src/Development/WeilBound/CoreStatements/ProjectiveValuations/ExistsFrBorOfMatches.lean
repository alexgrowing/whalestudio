import Development.WeilBound.CoreStatements.ProjectiveValuations.OpenImmersionCompStructureEqGeneric
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TendstoPowMulExp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramePointEigenframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLieEigenspaceFrameFlagCoverChartDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueWeightSectionFlagSpaceEqRuleAtFramedPoint

open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar.OntoDef GlobalTheory.CompHS
open GlobalTheory.CompanionTheory.Ar.HolExt

noncomputable section

namespace DifferentiableLines

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {r : ℕ} {σ : c.F →+* ℂ}

open Limits GlobalTheory.CxPts Filter Topology GlobalTheory.ShFam GlobalTheory.ShFam.BdArc GlobalTheory.Toroidal MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory Formalism.BasicNotions MonObj GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CovTop GlobalTheory.HSApp in

theorem exists_frBor_of_matches (T : TorFlag Xo c) {A : Type} [CommRing A] (q : Sp A ⟶ T.X.YY) (k : T.X.F.J)
    (hz : ⊤ ≤ q ⁻¹ᵁ T.X.F.U k) {φ : c.F →+* A} {x : Sp A ⟶ gen T.Y} (hx : q ≫ T.X.π = x ≫ genι T.Y)
    (fr : EigFrame T.Y φ (x ≫ genι T.Y))
    (hfr : ∀ τ j, fr.v τ j = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (T.X.F.vecAt k q hz hx τ j)).left) (ψ : A →+* CAt σ)
    {y : FrPt Xo c (CAt σ)} (hm : Matches fr ψ y) {z : Sp (CAt σ) ⟶ T.X.YY}
    (e : spMap ψ ≫ q = z) (hz' : ⊤ ≤ z ⁻¹ᵁ T.X.F.U k) :
    ∃ (Q : FrPt Xo c (CAt σ)) (t : Ix D → (CAt σ)ˣ), T.X.F.ChartFr k z hz' Q ∧ FrBor t Q y ∧ ∀ s, t (some s) = 1 := by
  subst e
  let z' : Sp (CAt σ) ⟶ T.X.YY := spMap ψ ≫ q
  have ex : spMap ψ ≫ (x ≫ genι T.Y) = z' ≫ T.X.π := by
    rw [← hx]; exact (Category.assoc _ _ _).symm
  have hxy : GlobalTheory.FlagMod.frX y ≫ T.Y.j = z' ≫ T.X.π := by
    calc GlobalTheory.FlagMod.frX y ≫ T.Y.j = (GlobalTheory.AllWt.ptF y ≫ T.Y.jQ) ≫ genι T.Y := by rw [Category.assoc]; rfl
    _ = spMap ψ ≫ (x ≫ genι T.Y) := (congrArg (· ≫ genι T.Y) hm.1).trans (Category.assoc _ _ _)
    _ = z' ≫ T.X.π := ex
  obtain ⟨Q, hQ⟩ := T.X.top.exists_chartFr (GlobalTheory.FlagMod.frX_snd y) hxy.symm k hz'
  have hv : ∀ τ j, GlobalTheory.FlagMod.frVec T.Y y hxy τ j = GlobalTheory.FlagMod.frVec T.Y Q hQ.over τ j := fun τ j => by
    rw [hQ.frVec_eq rfl hQ.over τ]
    refine (GlobalTheory.FlagMod.toModel_eq_iff _ _ _ _ _).2 ?_
    obtain ⟨w, h1, h2, h3⟩ := hm.2 τ j
    refine ⟨w, h1, h2, h3.trans ?_⟩
    rw [hfr τ j, ← T.X.F.tanPull_vecAt k ψ q hz hz' hx rfl ex]
    rfl
  have eQ : y.x = Q.x := by
    rw [← GlobalTheory.FlagMod.frX_fst, ← GlobalTheory.FlagMod.frX_fst,
      GlobalTheory.FlagMod.xF_ext (Y := T.Y) (GlobalTheory.FlagMod.frX_snd y) (GlobalTheory.FlagMod.frX_snd Q) (hxy.trans hQ.over.symm)]
  obtain ⟨u0, hu0⟩ := GlobalTheory.CompHS.BridgeValue.exists_gen_unit Q y eQ
  let t : Ix D → (CAt σ)ˣ := fun ix => ix.elim u0 fun _ => 1
  refine ⟨Q, t, hQ, GlobalTheory.FlagMod.frBor_of_frVec (T.X.F.inM hz' rfl) hQ.over hxy t (fun _ => 1)
    (fun _ => Matrix.blockTriangular_one) (fun _ i => Matrix.one_apply_eq i)
    (fun τ j => ?_) (fun _ => hu0), fun _ => rfl⟩
  rw [hv τ j]
  refine ((Fintype.sum_eq_single j fun j' hj' => ?_).trans ?_).symm
  · show (1 : Matrix (Fin (D.mult τ)) (Fin (D.mult τ)) (CAt σ)) j' j • _ = 0
    rw [Matrix.one_apply_ne hj', zero_smul]
  · show (1 : Matrix (Fin (D.mult τ)) (Fin (D.mult τ)) (CAt σ)) j j • _ = _
    rw [Matrix.one_apply_eq, one_smul]

theorem matches_of_sameLie {Z : Model Xo c (RingHom.id c.F)} {A : Type} [CommRing A] {φ : c.F →+* A} {x : Sp A ⟶ gen Z}
    {fr : EigFrame Z φ (x ≫ genι Z)} {ψ : A →+* ℂ} {y y' : FrPt Xo c (CAt σ)} (hm : Matches fr ψ y)
    (h : SameLie y' y) : Matches fr ψ y' := by
  have e : GlobalTheory.AllWt.ptF y' = GlobalTheory.AllWt.ptF y := by
    refine pullback.hom_ext ?_ ?_
    · exact (pullback.lift_fst _ _ _).trans (h.1.trans (pullback.lift_fst _ _ _).symm)
    · exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm
  refine ⟨e ▸ hm.1, fun τ i => ?_⟩
  rw [e, h.2 τ i]
  exact hm.2 τ i

theorem chr_of_some {e : Ix D → ℤ} {t : Ix D → (CAt σ)ˣ} (h : ∀ s, t (some s) = 1) :
    chr e t = toC (t none).val ^ e none := by
  classical
  have : (∏ ix, t ix ^ e ix) = t none ^ e none := by
    rw [Fintype.prod_option, Finset.prod_eq_one fun s _ => by rw [h, one_zpow], mul_one]
  exact (congrArg (fun u : (CAt σ)ˣ => toC u.val) this).trans (@Units.val_zpow_eq_zpow_val ℂ _ (t none) (e none))

theorem tendsto_punctured {f : ℂ → ℂ} (h : Tendsto (fun w => f (eTwoPi w)) imTop (𝓝 0)) :
    Tendsto f (𝓝[≠] 0) (𝓝 0) := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have t₁ : Tendsto (fun u : ℂ => Complex.log u / (2 * Real.pi * Complex.I)) (𝓝[≠] 0) imTop := by
    refine tendsto_comap_iff.2 ?_
    have h₁ : Tendsto (fun u : ℂ => ‖u‖) (𝓝[≠] 0) (𝓝[>] 0) := tendsto_norm_nhdsNE_zero
    have h₂ := (tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp h₁)).atTop_div_const hπ
    refine h₂.congr fun u => ?_
    have e : (2 * Real.pi * Complex.I : ℂ) = ((2 * Real.pi : ℝ) : ℂ) * Complex.I := by push_cast; ring
    simp only [Function.comp_apply]
    rw [e, ← div_div (Complex.log u), Complex.div_I, Complex.neg_im, Complex.mul_I_im, Complex.div_ofReal_re, Complex.log_re, neg_div]
  refine (h.comp t₁).congr' (eventually_mem_nhdsWithin.mono fun u hu => ?_)
  simp only [Function.comp_apply, eTwoPi]
  rw [mul_div_cancel₀ _ hne, Complex.exp_log hu]

set_option maxHeartbeats 800000 in

theorem exists_eigFrame_tau (T : TorFlag Xo c) {W : T.X.YY.Opens} (hW : IsAffineOpen W) [IsDomain Γ(T.X.YY, W)]
    {φ : c.F →+* Γ(T.X.YY, W)} (hφ : GlobalTheory.FlagMod.tau hW ≫ flagStr T.X = spMap φ) (k : T.X.F.J)
    (hz : ⊤ ≤ GlobalTheory.FlagMod.tau hW ⁻¹ᵁ T.X.F.U k) {x' : Sp Γ(T.X.YY, W) ⟶ T.Y.X} (hx : GlobalTheory.FlagMod.tau hW ≫ T.X.π = x') :
    ∃ fr : EigFrame T.Y φ x', ∀ τ j, fr.v τ j = (ReciprocityTheory.ChartRestriction.G.PullbackSections.tv (T.X.F.vecAt k _ hz hx τ j)).left := by
  subst hx
  let A : Type := Γ(T.X.YY, W)
  let K : Type := FractionRing A
  letI : Algebra c.F K := ((algebraMap A K).comp φ).toAlgebra
  let z : Sp K ⟶ T.X.YY := spMap (algebraMap A K) ≫ GlobalTheory.FlagMod.tau hW
  have hO : ⊤ ≤ z ⁻¹ᵁ flagOpen T.X := by
    intro s _
    let η : PrimeSpectrum A := ⟨⊥, Ideal.isPrime_bot⟩
    have hs : spMap (algebraMap A K) s = η := by
      refine PrimeSpectrum.ext ?_
      let s' : PrimeSpectrum K := s
      have h0 : s'.asIdeal = ⊥ := Ideal.eq_bot_of_prime _
      show Ideal.comap (algebraMap A K) s'.asIdeal = ⊥
      rw [h0]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective A K)
    obtain ⟨p, hpW, hpO⟩ := (dense_flagOpen T.X).inter_open_nonempty W W.isOpen
      ⟨_, GlobalTheory.FlagMod.tau_le hW le_rfl (Set.mem_univ η)⟩
    obtain ⟨p', rfl⟩ : p ∈ Set.range hW.fromSpec := hW.range_fromSpec.ge hpW
    have hsp : η ⤳ (p' : PrimeSpectrum A) := (PrimeSpectrum.le_iff_specializes _ _).1 bot_le
    show GlobalTheory.FlagMod.tau hW (spMap (algebraMap A K) s) ∈ flagOpen T.X
    rw [hs]
    exact (hsp.map (GlobalTheory.FlagMod.tau hW).continuous).mem_open (flagOpen T.X).isOpen hpO
  have hr : Set.range (z ≫ T.X.π) ⊆ Set.range T.Y.j := by
    rintro _ ⟨s, rfl⟩
    exact hO (Set.mem_univ s)
  have hf := IsOpenImmersion.lift_fac T.Y.j (z ≫ T.X.π) hr
  refine GlobalTheory.ChartEigFrame.exists_eigFrame_vecAt E H D l Xo c _ _ T.Y T.X A K φ rfl _ k hz
    (IsOpenImmersion.lift T.Y.j (z ≫ T.X.π) hr) ?_ hf.symm
  rw [← openImmersion_comp_structure_eq_generic T.Y, ← Category.assoc, hf, Category.assoc, Category.assoc]
  exact (congrArg (_ ≫ ·) hφ).trans (Spec.map_comp _ _).symm

set_option maxHeartbeats 800000 in

theorem tendsto_arc_reads {V : Unf Xo c σ r} (hσ : GoodEmb c σ) (hU : IsUnf V) (T : TorFlag Xo c)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {k : V.Comp} {P : Frame (V.X k).Ψ r → ℂ}
    (hP : P ∈ (V.X k).SS (laU V a n k))
    {h : (T.X.LL fun i => (ex D a n i : ℤ)).ι → GlobalTheory.CxPts (flagStr T.X) σ → ℂ}
    (hR : Reads V T (fun i => (ex D a n i : ℤ)) k P h) (hZ : OffZero V T k h)
    {e' : Ix D → ℤ} (he' : e' none = 8) {K : Rul Xo c} (hK : K ∈ extZ T.X e') {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hlow : ∀ x : (V.X k).dom, c₀ ≤ ‖toC (evR Xo c K (V.un k x))‖) (i : T.X.F.J)
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
  obtain ⟨C', B, hn⟩ := GlobalTheory.T.period_frame_limits_of_orbit E r _ T₀ M γ xx (laU V a n k') m v Lp Lm hO (fun τ j => ⟨fun h => by
    simp only [laU, if_pos h]; positivity, fun h => by simp only [laU, if_neg (not_le.2 h)]; omega⟩) hlim
  have hp := tendsto_cusp hP hO.2.2.2.1 hξ hc' ht hn
  obtain ⟨S, rfl⟩ := hK
  let f : Γ(T.X.YY, W) := resG T.X.YY (le_inf le_top hWi : W ≤ ⊤ ⊓ T.X.F.U i) (S.loc i)
  have hcont : ContinuousAt (fun u => ev _ σ W f (s u)) 0 :=
    ((hsd f).differentiableAt (Metric.ball_mem_nhds 0 hρ)).continuousAt
  have he0 : Tendsto eTwoPi imTop (𝓝 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.2 ?_
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      ((tendsto_comap (f := Complex.im)).const_mul_atTop (show 0 < 2 * Real.pi by positivity))
    refine this.congr fun w => ?_
    simp [eTwoPi, Complex.norm_exp]
  set N : ℝ := ‖ev _ σ W f (s 0)‖ + 1 with hN
  have hN0 : 0 < N := by positivity
  have hbd : ∀ᶠ w in imTop, ‖ev _ σ W f (s (eTwoPi w))‖ < N :=
    (hcont.tendsto.comp he0).norm.eventually (gt_mem_nhds (lt_add_one _))
  set μ : ℝ := min 1 (c₀ / N) with hμ
  have hμ0 : 0 < μ := lt_min one_pos (div_pos hc₀ hN0)
  have hlim0 := hp.norm.mul_const (μ ^ n)⁻¹
  rw [norm_zero, zero_mul] at hlim0
  refine squeeze_zero_norm' ?_ hlim0
  filter_upwards [hev, hbd] with w hw hw'
  obtain ⟨hd, Q, t, hQ, ht, ht1⟩ := hfb w hw
  have hu := hT w hw
  have e₁ : P (xx w) = chr (fun i => (ex D a n i : ℤ)) t * h i (s (eTwoPi w)) :=
    hR (xx w) hd i _ (hi _ hu) Q t (GlobalTheory.FlagMod.FlagCover.eq_ptY (hQ.lies.frBor ht)).symm hQ ht
  have : _root_.IsReduced (CAt σ) := (inferInstance : _root_.IsReduced ℂ)
  have e₂ : toC (evR Xo c (ruleTop T.X e' S) (V.un k' ⟨_, hd⟩)) = chr e' t * ev _ σ W f (s (eTwoPi w)) := by
    refine (congrArg toC (evR_ruleTop (z := zOf (s (eTwoPi w))) S (h1 _ hu (hne0 w)) hQ ht)).trans (congrArg (chr e' t * ·) ?_)
    have hm' : s (eTwoPi w) ∈ ptsIn (flagStr T.X) σ (⊤ ⊓ T.X.F.U i) :=
      ptsIn_mono (le_inf le_top hWi) (hsW _ hu)
    exact (ev_eq hm' (S.loc i)).symm.trans
      (ev_res (le_inf le_top hWi : W ≤ ⊤ ⊓ T.X.F.U i) (hsW _ hu) (S.loc i)).symm
  rw [chr_of_some ht1] at e₁ e₂
  set τ : ℂ := toC (t none).val
  have a₁ : ‖P (xx w)‖ = ‖τ‖ ^ n * ‖h i (s (eTwoPi w))‖ := by
    rw [e₁, norm_mul, norm_zpow]
    exact congrArg (· * _) (zpow_natCast _ _)
  have a₂ : c₀ ≤ ‖τ‖ ^ 8 * N := by
    refine (hlow ⟨_, hd⟩).trans ?_
    rw [e₂, he', norm_mul, norm_zpow, show ((8 : ℤ)) = ((8 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact mul_le_mul_of_nonneg_left hw'.le (by positivity)
  have a₃ : μ ≤ ‖τ‖ := by
    rcases le_total 1 ‖τ‖ with h' | h'
    · exact (min_le_left _ _).trans h'
    · refine (min_le_right _ _).trans ((div_le_iff₀ hN0).2 (a₂.trans ?_))
      exact mul_le_mul_of_nonneg_right (pow_le_of_le_one (norm_nonneg _) h' (by norm_num)) hN0.le
  rw [a₁, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hμ0 n), mul_comm]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hμ0.le a₃ n) (norm_nonneg _)

end DifferentiableLines
