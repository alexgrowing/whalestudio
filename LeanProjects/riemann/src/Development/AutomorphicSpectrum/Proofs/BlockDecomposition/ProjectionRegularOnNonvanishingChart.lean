import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatiosEqOfSameOrbit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexPointLiftsToMulticoneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointsEqIffSameTorusOrbitStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnderOfSameOrbitStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PointIdealMultiprojectivePrime
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsSheetOnlyNull
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartZeroSet
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ.ArchEq.PieceAt

open Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (scaleBlock scaleBlock_mem_zeroLocus eval_scaleBlock segre_differentiableAt)
open GroundTheory.Heights₂.Heights.PtsSheetOnlyNull (ratio inv_smul_eq_cons segre_scaleBlock differentiableAt_ratio)

variable {m : ℕ} {n : Fin (m + 1) → ℕ} {D : ℕ}

theorem exists_localInverse {O : Set (Fin D → ℂ)} (hO : IsOpen O) {τ : (Fin D → ℂ) → Fin D → ℂ}
    (hτ : DifferentiableOn ℂ τ O) {v₀ : Fin D → ℂ} (hv : v₀ ∈ O)
    (hdet : LinearMap.det (fderiv ℂ τ v₀ : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)) ≠ 0) :
    ∃ φ : OpenPartialHomeomorph (Fin D → ℂ) (Fin D → ℂ), v₀ ∈ φ.source ∧ φ.source ⊆ O ∧
      (∀ v, φ v = τ v) ∧ DifferentiableOn ℂ φ.symm φ.target := by
  have hτa : AnalyticAt ℂ τ v₀ :=
    GroundTheory.Heights₂.Heights.SheetOnlyNull.analyticOnNhd_of_differentiableOn hO hτ v₀ hv
  have hτc : ContDiffAt ℂ 1 τ v₀ := hτa.contDiffAt
  have hinj : Function.Injective (fderiv ℂ τ v₀ : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)) :=
    ((Module.End.isUnit_iff _).1 ((LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))).1
  set L := (LinearEquiv.ofInjectiveEndo (fderiv ℂ τ v₀ : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))
    hinj).toContinuousLinearEquiv with hLdef
  have hτL : HasFDerivAt τ (L : (Fin D → ℂ) →L[ℂ] (Fin D → ℂ)) v₀ :=
    hτa.differentiableAt.hasFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun v => rfl)
  set φ := hτc.toOpenPartialHomeomorph τ hτL one_ne_zero with hφdef
  have hφτ : ∀ v, φ v = τ v := fun v => rfl
  have hsrc : v₀ ∈ φ.source := hτc.mem_toOpenPartialHomeomorph_source hτL one_ne_zero
  have htgt : τ v₀ ∈ φ.target := hτc.image_mem_toOpenPartialHomeomorph_target hτL one_ne_zero
  have hsymm : φ.symm (τ v₀) = v₀ := φ.left_inv hsrc
  have hsymmc : ContDiffAt ℂ 1 φ.symm (τ v₀) :=
    φ.contDiffAt_symm (f₀' := L) htgt (by rw [hsymm]; exact hτL) (by rw [hsymm]; exact hτc)
  have hev_O : ∀ᶠ t in 𝓝 (τ v₀), φ.symm t ∈ O :=
    hsymmc.continuousAt.preimage_mem_nhds (by rw [hsymm]; exact hO.mem_nhds hv)
  have hev_d : ∀ᶠ t in 𝓝 (τ v₀), DifferentiableAt ℂ φ.symm t :=
    (hsymmc.eventually (by simp)).mono fun t ht => ht.differentiableAt one_ne_zero
  set T : Set (Fin D → ℂ) := interior {t | φ.symm t ∈ O ∧ DifferentiableAt ℂ φ.symm t} with hT
  have hTo : IsOpen T := isOpen_interior
  have hτT : τ v₀ ∈ T := mem_interior_iff_mem_nhds.2 (hev_O.and hev_d)
  have hTs : ∀ t ∈ T, φ.symm t ∈ O ∧ DifferentiableAt ℂ φ.symm t := fun t ht => (interior_subset ht : t ∈ {t | φ.symm t ∈ O ∧ DifferentiableAt ℂ φ.symm t})
  refine ⟨(φ.symm.restrOpen T hTo).symm, ?_, ?_, fun v => rfl, ?_⟩
  · exact ⟨hsrc, hτT⟩
  · rintro v ⟨hv1, hv2⟩
    have := (hTs _ hv2).1
    rwa [φ.symm.right_inv hv1] at this
  · rintro t ⟨-, ht⟩
    exact (hTs t ht).2.differentiableWithinAt

def ratioFn {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) (p : ∀ k, Bk n k) (q : Σ k, Bk n k) :
    Γ(X, i ⁻¹ᵁ blockChart n q.1 (p q.1)) :=
  i.app _ (pullRatio (prB n q.1) _ (p q.1) le_rfl q.2)

def vecAt {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) (p : ∀ k, Bk n k) (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) :
    (Σ k, Bk n k) → ℂ :=
  fun q => ev (i ≫ mpStr ℤ m n) σ₀ _ (ratioFn i p q) y

theorem vecAt_apply {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) (p : ∀ k, Bk n k)
    (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (q : Σ k, Bk n k) :
    vecAt i p y q = ev (mpStr ℤ m n) σ₀ (blockChart n q.1 (p q.1))
      (pullRatio (prB n q.1) _ (p q.1) le_rfl q.2) (PtsOver.map i rfl _ y) :=
  ev_app i rfl _ _ y

theorem eq_scale_vecAt {X : Scheme.{0}} {i : X ⟶ MP ℤ m n} {p : ∀ k, Bk n k}
    {y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (h : Over i y z)
    (hp : ∀ k, z ⟨k, p k⟩ ≠ 0) : (fun q : Σ k, Bk n k => z ⟨q.1, p q.1⟩ * vecAt i p y q) = z := by
  funext ⟨k, j⟩
  show z ⟨k, p k⟩ * vecAt i p y ⟨k, j⟩ = z ⟨k, j⟩
  rw [vecAt_apply]
  show z ⟨k, p k⟩ * ev (mpStr ℤ m n) σ₀ (blockChart n k (p k)) (pullRatio (prB n k) _ (p k) le_rfl j)
    (PtsOver.map i rfl _ y) = _
  rw [(h k (p k)).2 j ((h k (p k)).1.2 (hp k))]
  field_simp [hp k]

theorem over_scale_vecAt {X : Scheme.{0}} [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (p : ∀ k, Bk n k) {y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀}
    (hy : ∀ k, PtsOver.map i rfl _ y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k (p k)))
    (b : Fin (m + 1) → ℂ) (hb : ∀ k, b k ≠ 0) :
    Over i y (fun q => b q.1 * vecAt i p y q) ∧
      (fun q : Σ k, Bk n k => b q.1 * vecAt i p y q) ∈ mcPts (ptIdeal (i (genericPoint X))) := by
  obtain ⟨z', hz', hU⟩ := GlobalTheory.T.complex_point_lifts_to_multicone m n X i y
  have hne : ∀ k, z' ⟨k, p k⟩ ≠ 0 := fun k => (hU k (p k)).1.1 (hy k)
  have hc : ∀ k, b k / z' ⟨k, p k⟩ ≠ 0 := fun k => div_ne_zero (hb k) (hne k)
  have e : (fun q : Σ k, Bk n k => b q.1 * vecAt i p y q) =
      fun q : Σ k, Bk n k => (fun k => b k / z' ⟨k, p k⟩) q.1 * z' q := by
    funext q
    have h1 := eq_scale_vecAt (p := p) hU hne
    have h2 := congrFun h1 q
    have h3 := hne q.1
    simp only [] at h2 ⊢
    rw [← h2]
    field_simp
  rw [e]
  exact ⟨GlobalTheory.T.isUnder_of_same_orbit m n _ z' _ hU ⟨_, hc, rfl⟩,
    GroundTheory.Heights₂.Heights.SegreChartZeroSet.scaleAll_mem _ (isMultiProjPrime_ptIdeal m n _).2.1 _ hc hz'⟩

theorem over_liftOf {X : Scheme.{0}} {i : X ⟶ MP ℤ m n} {y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀}
    {z : (Σ k, Bk n k) → ℂ} (h : Over i y z) : Over i y (liftOf i y) := by
  have hex : ∃ z, Over i y z := ⟨z, h⟩
  rw [liftOf, dif_pos hex]
  exact hex.choose_spec

theorem differentiableOn_vecAt {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) (p : ∀ k, Bk n k)
    (c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D) :
    DifferentiableOn ℂ (fun v => vecAt i p (c.finChart.symm v))
      (c.finChart.target ∩ c.finChart.symm ⁻¹' ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart p)) := by
  refine differentiableOn_pi.2 fun q => ?_
  have h := (c.analyticOnNhd_finChart_iff (isOpen_ptsIn (i ⁻¹ᵁ blockChart n q.1 (p q.1)))
    (ev (i ≫ mpStr ℤ m n) σ₀ _ (ratioFn i p q))).2 (c.holo _ _)
  refine h.differentiableOn.mono fun v hv => ⟨hv.1, ?_⟩
  exact GlobalTheory.CxPts.ptsIn_mono (Scheme.Hom.preimage_mono i (mchart_le p q.1)) hv.2

theorem mem_pieceSet : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ)
    (Ψ : GlobalTheory.CompanionTheory.MixZ.ArchEq.LinProj n D) (N : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog N a →
    ∀ (c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D) (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (z : (Σ k, Bk n k) → ℂ),
      y ∈ c.e.source → GlobalTheory.CompanionTheory.MixZ.ArchEq.Over i y z → eval z (map (Int.castRingHom ℂ) N) ≠ 0 → Ψ (segre z) 0 ≠ 0 →
      GlobalTheory.CompanionTheory.MixZ.ArchEq.IsRegAt i Ψ c y → y ∈ GlobalTheory.CompanionTheory.MixZ.ArchEq.pieceSet i Ψ N := by
  intro m n X _ i _ D Ψ N a hN c y z hyc hz hNz h0 hreg
  choose p hp using fun k => GlobalTheory.CompanionTheory.MixZ.Orbit.exists_ne_zero_of_isUnder hz k
  have hyk : ∀ k, PtsOver.map i rfl _ y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k (p k)) :=
    fun k => (hz k (p k)).1.2 (hp k)

  have hy0 : y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart p) := by
    refine GlobalTheory.CxPts.mem_ptsIn.2 (Set.mem_iInter.2 fun k => ?_)
    exact GlobalTheory.CxPts.mem_ptsIn.1 (hyk k)
  set v₀ := c.finChart y with hv₀
  have hsymm0 : c.finChart.symm v₀ = y := c.finChart.left_inv hyc
  let lam : (Fin D → ℂ) → (Σ k, Bk n k) → ℂ :=
    fun v q => z ⟨q.1, p q.1⟩ * vecAt i p (c.finChart.symm v) q
  let S : Set (Fin D → ℂ) :=
    c.finChart.target ∩ c.finChart.symm ⁻¹' ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart p)
  have hSo : IsOpen S := c.finChart.isOpen_inter_preimage_symm (isOpen_ptsIn _)
  have hv₀S : v₀ ∈ S := ⟨c.finChart.map_source hyc, by
    change c.finChart.symm v₀ ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart p)
    rw [hsymm0]; exact hy0⟩
  have hlamd : ∀ v ∈ S, DifferentiableAt ℂ lam v := by
    intro v hv
    have h1 := (differentiableOn_vecAt i p c).differentiableAt (hSo.mem_nhds hv)
    refine differentiableAt_pi.2 fun q => ?_
    exact (differentiableAt_const _).fun_mul (differentiableAt_pi.1 h1 q)
  have hlam0 : lam v₀ = z := by
    have := eq_scale_vecAt (p := p) hz hp
    funext q
    have h2 := congrFun this q
    show z ⟨q.1, p q.1⟩ * vecAt i p (c.finChart.symm v₀) q = z q
    rw [hsymm0]; exact h2
  let F : (Fin D → ℂ) → ℂ := fun v => Ψ (segre (lam v)) 0 * eval (lam v) (map (Int.castRingHom ℂ) N)
  have hFc : ContinuousOn F S := by
    intro v hv
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : DifferentiableAt ℂ (fun v => Ψ (segre (lam v))) v :=
      GroundTheory.Heights₂.Heights.PtsSheetOnlyNull.differentiableAt_proj_segre Ψ (hlamd v hv)
    have h2 : ContinuousAt (fun v => Ψ (segre (lam v)) 0) v := (differentiableAt_pi.1 h1 0).continuousAt
    have h3 : ContinuousAt (fun v => eval (lam v) (map (Int.castRingHom ℂ) N)) v :=
      (MvPolynomial.continuous_eval _).continuousAt.comp (hlamd v hv).continuousAt
    exact h2.mul h3
  let O : Set (Fin D → ℂ) := S ∩ F ⁻¹' {0}ᶜ
  have hOo : IsOpen O := hFc.isOpen_inter_preimage hSo isOpen_compl_singleton
  have hv₀O : v₀ ∈ O := ⟨hv₀S, by
    show F v₀ ≠ 0
    simp only [F, hlam0]
    exact mul_ne_zero h0 hNz⟩
  have hΨ0 : ∀ v ∈ O, Ψ (segre (lam v)) 0 ≠ 0 := fun v hv => left_ne_zero_of_mul hv.2
  have hNv : ∀ v ∈ O, eval (lam v) (map (Int.castRingHom ℂ) N) ≠ 0 :=
    fun v hv => right_ne_zero_of_mul hv.2
  have hchart : ∀ v ∈ S, ∀ k, PtsOver.map i rfl _ (c.finChart.symm v) ∈
      ptsIn (mpStr ℤ m n) σ₀ (blockChart n k (p k)) := fun v hv k =>
    GlobalTheory.CxPts.ptsIn_mono (mchart_le p k) hv.2
  have hlamU : ∀ v ∈ S, Over i (c.finChart.symm v) (lam v) ∧
      lam v ∈ mcPts (ptIdeal (i (genericPoint X))) := fun v hv =>
    over_scale_vecAt i p (hchart v hv) (fun k => z ⟨k, p k⟩) hp
  have hτ : ∀ v ∈ O, projCoord i Ψ (c.finChart.symm v) = ratios Ψ (lam v) := by
    intro v hv
    have h1 := (hlamU v hv.1).1
    have h2 := over_liftOf h1
    exact ratios_eq_of_sameOrbit Ψ
      ((GlobalTheory.T.points_eq_iff_same_torus_orbit m n X i _ _ _ _ h2 h1).1 rfl) (hΨ0 v hv)
  have hτd : DifferentiableOn ℂ (projCoord i Ψ ∘ c.finChart.symm) O := by
    intro v hv
    have h1 : DifferentiableAt ℂ (fun v' => ratio (Ψ (segre (lam v')))) v :=
      differentiableAt_ratio Ψ (hlamd v hv.1) (hΨ0 v hv)
    refine (h1.congr_of_eventuallyEq ?_).differentiableWithinAt
    filter_upwards [hOo.mem_nhds hv] with v' hv'
    exact hτ v' hv'
  obtain ⟨φ, hφ0, hφO, hφτ, hφd⟩ := exists_localInverse hOo hτd hv₀O hreg
  have hφt : ∀ t ∈ φ.target, φ.symm t ∈ O := fun t ht => hφO (φ.map_target ht)
  have hφr : ∀ t ∈ φ.target, ratios Ψ (lam (φ.symm t)) = t := by
    intro t ht
    have h1 := hτ _ (hφt t ht)
    have h2 := hφτ (φ.symm t)
    rw [φ.right_inv ht] at h2
    exact (h2.trans h1).symm
  refine ⟨c.finChart.trans φ, fun t => scaleBlock 0 (Ψ (segre (lam (φ.symm t))) 0)⁻¹ (lam (φ.symm t)),
    ⟨⟨c, fun w hw => ?_⟩, ?_, ?_⟩, ?_⟩
  · rw [OpenPartialHomeomorph.trans_source] at hw
    exact hw.1
  · intro t ht
    rw [OpenPartialHomeomorph.trans_target] at ht
    have htt := ht.1
    have hO' := hφt t htt
    have hd1 : DifferentiableAt ℂ φ.symm t := (hφd t htt).differentiableAt (φ.open_target.mem_nhds htt)
    have hg : DifferentiableAt ℂ (fun t => lam (φ.symm t)) t := (hlamd _ hO'.1).comp t hd1
    have hp1 : DifferentiableAt ℂ (fun v => Ψ (segre (lam v))) (φ.symm t) :=
      GroundTheory.Heights₂.Heights.PtsSheetOnlyNull.differentiableAt_proj_segre Ψ (hlamd _ hO'.1)
    have hc : DifferentiableAt ℂ (fun t => (Ψ (segre (lam (φ.symm t))) 0)⁻¹) t :=
      ((differentiableAt_pi.1 hp1 0).fun_inv (hΨ0 _ hO')).comp t hd1
    refine DifferentiableAt.differentiableWithinAt (differentiableAt_pi.2 fun q => ?_)
    simp only [scaleBlock]
    split_ifs
    · exact hc.fun_mul (differentiableAt_pi.1 hg q)
    · exact (differentiableAt_const _).fun_mul (differentiableAt_pi.1 hg q)
  · intro t ht
    rw [OpenPartialHomeomorph.trans_target] at ht
    have htt := ht.1
    have hO' := hφt t htt
    have hsy : (c.finChart.trans φ).symm t = c.finChart.symm (φ.symm t) := rfl
    have hcne := inv_ne_zero (hΨ0 _ hO')
    obtain ⟨hU, hM⟩ := hlamU _ hO'.1
    have hG : scaleBlock (0 : Fin (m + 1)) (Ψ (segre (lam (φ.symm t))) 0)⁻¹ (lam (φ.symm t)) =
        fun q => (fun k : Fin (m + 1) => if k = 0 then (Ψ (segre (lam (φ.symm t))) 0)⁻¹ else 1) q.1 *
          lam (φ.symm t) q := rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hsy]
      refine GlobalTheory.T.isUnder_of_same_orbit m n _ _ _ hU ⟨fun k : Fin (m + 1) => if k = 0 then (Ψ (segre (lam (φ.symm t))) 0)⁻¹ else 1, fun k => ?_, hG⟩
      dsimp only
      split_ifs
      · exact hcne
      · exact one_ne_zero
    · exact scaleBlock_mem_zeroLocus _ (isMultiProjPrime_ptIdeal m n _).2.1 0 hcne hM
    · simp only [segre_scaleBlock, map_smul]
      rw [inv_smul_eq_cons _ (hΨ0 _ hO')]
      exact congrArg _ (hφr t htt)
    · rw [eval_scaleBlock 0 _ _ N a hN]
      exact mul_ne_zero (pow_ne_zero _ hcne) (hNv _ hO')
  · rw [OpenPartialHomeomorph.trans_source]
    exact ⟨hyc, hφ0⟩

end GlobalTheory.CompanionTheory.MixZ.ArchEq.PieceAt
