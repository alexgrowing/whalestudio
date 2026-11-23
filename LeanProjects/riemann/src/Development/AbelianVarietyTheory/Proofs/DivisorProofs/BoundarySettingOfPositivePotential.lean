import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondChernDensity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareFormStatementStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncatedPlurisubharmonicCorrection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalModelChartFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousOnFrameDirectionsInverse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeNearPoint
import ReciprocityTheory.AnalyticForms.PotentialTheory.MaMeasureA

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArchLim.CurvFam

section Frames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open ReciprocityTheory.ChartRestriction.G.PullbackSections Filter
open scoped Matrix CategoryTheory.Obj Topology

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem snd_valR_comb {X : Scheme.{0}} {t : SAB H X} {x : Sp ℂ ⟶ X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber ℂ) ⟶ t.G.left)} (ht : ∀ i, IsTanAtG t x (v i)) {a : Fin m → ℂ}
    {v' : Sp (DualNumber ℂ) ⟶ t.G.left} (ht' : IsTanAtG t x v') (hc : IsCombAtG t x v a v') (U : t.G.left.Opens)
    (h : ⊤ ≤ v' ⁻¹ᵁ U) (f : Γ(t.G.left, U)) :
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR (A := DualNumber ℂ) v' U f).snd =
      ∑ i, a i * (ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR (A := DualNumber ℂ) (v i) U f).snd := by
  have hU : ∀ i, ⊤ ≤ v i ⁻¹ᵁ U := fun i => DerLin.le_of_fst_eq ((ht i).2.trans ht'.2.symm) h
  let b : Fin m → TanMod.TanSp x t.G := fun i =>
    TanMod.TanSp.mk (Over.homMk (v i) (ht i).1) (TanMod.smT_zero_of x _ (ht i).2)
  have key : (TanDeriv.evAt v' U h f).snd = ∑ i, a i * (TanDeriv.evAt (v i) U (hU i) f).snd := by
    refine TanDeriv.derivAt_sum b a v' ?_ U h hU f
    obtain ⟨u, hu, rfl⟩ := hc
    have hub : u = fun i => (a i • b i).pt := funext fun i => Over.OverMorphism.ext (hu i)
    subst hub
    rw [List.prod_ofFn, ← TanMod.TanSp.pt_sum]
  simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR, dif_pos h, dif_pos (hU _)]
  exact key

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {σ : c.F →+* ℂ}

theorem eq_zero_of_snd {x : Sp ℂ ⟶ Z.X} (f : EigFrame Z σ x) (τ : E →+* ℂ) (w : Fin (Dw.mult τ) → ℂ)
    (hw : ∀ (U : Z.t.G.left.Opens) (r : Γ(Z.t.G.left, U)),
      ⊤ ≤ (show Sp ℂ ⟶ Z.t.G.left from (1 : Over.mk x ⟶ Z.t.G).left) ⁻¹ᵁ U →
      ∑ i, w i * (ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR (A := DualNumber ℂ) (f.v τ i) U r).snd = 0) : w = 0 := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤)
    (x := (show Sp ℂ ⟶ Z.t.G.left from (1 : Over.mk x ⟶ Z.t.G).left) (IsLocalRing.closedPoint ℂ)) trivial
  have h1 : ⊤ ≤ (show Sp ℂ ⟶ Z.t.G.left from (1 : Over.mk x ⟶ Z.t.G).left) ⁻¹ᵁ U := (Points.le_preimage_iff _ _).2 hx
  have hin : ∀ u : TanM x Z.t.G, ⊤ ≤ (show Sp (DualNumber ℂ) ⟶ Z.t.G.left from (tv u).left) ⁻¹ᵁ U := fun u =>
    (TangentOrigin.top_le_preimage_iff _ U).2 (by rw [(isTan_tv u).2]; exact h1)
  have hs := fun (a : Fin (Dw.mult τ) → ℂ) r => snd_valR_comb (f.tan τ) (isTan_tv (∑ i, a i • f.vec τ i))
    ((isComb_iff (f.vec τ) a _).2 rfl) U (hin _) r
  have he : (∑ i, w i • f.vec τ i) = ∑ i, (0 : Fin (Dw.mult τ) → ℂ) i • f.vec τ i := by
    refine tan_ext (TangentOrigin.ext_evalPt hU (hin _) (hin _) (RingHom.ext fun r => TrivSqZeroExt.ext ?_ ?_))
    · have e := fun u : TanM x Z.t.G => TangentOrigin.evalPt_spMap_comp TangentOrigin.fstC _ U (hin u)
        ((TangentOrigin.top_le_preimage_iff _ U).1 (hin u)) r
      refine (e _).symm.trans (Eq.trans ?_ (e _))
      exact TanDeriv.evAt_congr ((isTan_tv _).2.trans (isTan_tv _).2.symm) U _ _ r
    · have a1 := (hs w r).trans (hw U r h1)
      have a2 := (hs 0 r).trans (Finset.sum_eq_zero fun i _ => zero_mul _)
      rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR, dif_pos (hin _)] at a1 a2
      exact a1.trans a2.symm
  exact funext (Fintype.linearIndependent_iff.1 (f.linearIndependent_vec τ) w (by simpa using he))

theorem differentiableAt_co {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {B : Set V}
    {x : V → CxPts (genStr Z) σ} {f g : ∀ b, EigFrame Z σ ((x b).1 ≫ genι Z)} (hf : HolFam B fun b => ⟨x b, f b⟩)
    (hg : HolFam B fun b => ⟨x b, g b⟩) (τ : E →+* ℂ) (k i : Fin (Dw.mult τ)) {b₀ : V} (hb₀ : b₀ ∈ B) :
    DifferentiableAt ℂ (fun b => (f b).co (g b) τ k i) b₀ := by
  refine differentiableAt_pi.1 (HolLieFrame.differentiableAt_of_forms (fun b k => (f b).co (g b) τ k i) b₀
    fun w hw => eq_zero_of_snd (f b₀) τ w fun U r hU => ?_) k
  have h1 : IsHolTo B fun b => (show Sp ℂ ⟶ Z.t.G.left from (1 : Over.mk ((x b).1 ≫ genι Z) ⟶ Z.t.G).left) :=
    LocLift.isHolTo_comp_hom (LocLift.isHolTo_comp_hom hf.1 (genι Z)) (η[Z.t.G]).left
  have hn := LocalLift.hol_eventually_mem h1 hb₀ hU
  have hin : ∀ {b} {v : Sp (DualNumber ℂ) ⟶ Z.t.G.left}, IsTanAtG Z.t ((x b).1 ≫ genι Z) v →
      ⊤ ≤ (show Sp ℂ ⟶ Z.t.G.left from (1 : Over.mk ((x b).1 ≫ genι Z) ⟶ Z.t.G).left) ⁻¹ᵁ U → ⊤ ≤ v ⁻¹ᵁ U :=
    fun hv h => (TangentOrigin.top_le_preimage_iff _ U).2 (by rw [hv.2]; exact h)
  have d1 := fun a => (hf.2 τ a U r).differentiableAt (x := b₀) (hn.mono fun b hb => ⟨hb.1, hin ((f b).tan τ a) hb.2⟩)
  have d2 := (hg.2 τ i U r).differentiableAt (x := b₀) (hn.mono fun b hb => ⟨hb.1, hin ((g b).tan τ i) hb.2⟩)
  have := hw (fun b => ∑ a, (ReciprocityTheory.ChartRestriction.G.Geo.Tor.valR (A := DualNumber ℂ) ((f b).v τ a) U r).snd •
      (ContinuousLinearMap.proj a : (Fin (Dw.mult τ) → ℂ) →L[ℂ] ℂ))
    (DifferentiableAt.fun_sum fun a _ => (d1 a).smul_const _) (d2.congr_of_eventuallyEq ?_)
  · simpa [mul_comm] using this
  · filter_upwards [hn] with b hb
    rw [snd_valR_comb ((f b).tan τ) ((g b).tan τ i) ((f b).co_spec (g b) τ i) U (hin ((g b).tan τ i) hb.2)]
    simp [mul_comm]

theorem exists_alg_frame (y₀ : CxPts (genStr Z) σ) : ∃ (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1))
    (F : EigFrame Z φ (LogKS.chart V ≫ genι Z)), LogKS.chart V ≫ genStr Z = spMap φ ∧ y₀ ∈ ptsIn (genStr Z) σ V.1 ∧
    ∀ (y : CxPts (genStr Z) σ) (hy : y ∈ ptsIn (genStr Z) σ V.1),
      ∃ f : EigFrame Z σ (y.1 ≫ genι Z), F.IsMap (evHom hy) f := by
  obtain ⟨U, hU, φ, F, hzU, hφ, -⟩ :=
    EigSpread.exists_stable_eigFrame E H Dw l Xo c O β Z (y₀.1 (IsLocalRing.closedPoint ℂ))
  let V : (gen Z).affineOpens := ⟨U, hU⟩
  have hφ' : LogKS.chart V ≫ genStr Z = spMap φ := hφ
  refine ⟨V, φ, F, hφ', CxPts.mem_ptsIn.2 hzU, fun y hy => EigFrame.exists_isMap F (evHom hy) ?_ ?_⟩
  · exact EigLoc.spMap_inj (y.2.symm.trans (by
      rw [← ReciprocityTheory.ChartRestriction.G.PullbackSections.spMap_comp_spMap, ← hφ', ← Category.assoc, spMap_evHom hy]))
  · exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ genι Z) (spMap_evHom hy))).symm

theorem exists_frames [SmoothOfRelativeDimension Dw.dim (genStr Z)] (y₀ : CxPts (genStr Z) σ) :
    ∃ (W : Set (CxPts (genStr Z) σ)) (g : ∀ y : CxPts (genStr Z) σ, EigFrame Z σ (y.1 ≫ genι Z)), IsOpen W ∧ y₀ ∈ W ∧
      (∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (B : Set V) (y : V → CxPts (genStr Z) σ), IsOpen B →
        IsHolTo B (fun b => (y b).1) → Set.MapsTo y B W → HolFam B fun b => ⟨y b, g (y b)⟩) ∧
      ∀ G : EigMet Z σ, G.SmoothOn (manifold Z σ) Set.univ → ∀ τ k k',
        (manifold Z σ).SmoothOn W (fun y => (G.gram y (g y) τ k k').re) ∧
        (manifold Z σ).SmoothOn W (fun y => (G.gram y (g y) τ k k').im) := by
  classical
  obtain ⟨U, φ, F, hφ, hy₀, hfr⟩ := exists_alg_frame y₀
  choose fr hfr using hfr
  have hne : ∀ y : CxPts (genStr Z) σ, Nonempty (EigFrame Z σ (y.1 ≫ genι Z)) := fun y =>
    have ⟨_, _, _, _, h, h'⟩ := exists_alg_frame y
    ⟨(h' y h).choose⟩
  let g : ∀ y : CxPts (genStr Z) σ, EigFrame Z σ (y.1 ≫ genι Z) := fun y =>
    if h : y ∈ ptsIn (genStr Z) σ U.1 then fr y h else (hne y).some
  have hg : ∀ y (h : y ∈ ptsIn (genStr Z) σ U.1), F.IsMap (evHom h) (g y) := fun y h => by
    rw [show g y = fr y h from dif_pos h]; exact hfr y h
  refine ⟨_, g, isOpen_ptsIn U.1, hy₀, fun V _ _ B y hB hy hm => ⟨hy, fun ρ i => ?_⟩, fun G hG τ k k' => ?_⟩
  · let ev : V → (Γ(gen Z, U.1) →+* ℂ) := fun b =>
      if h : y b ∈ ptsIn (genStr Z) σ U.1 then evHom h else evHom hy₀
    have hev : ∀ b (h : y b ∈ ptsIn (genStr Z) σ U.1), ev b = evHom h := fun b h => dif_pos h
    have : IsOpenImmersion (LogKS.chart U) := IsAffineOpen.isOpenImmersion_fromSpec U.2
    have hd : ∀ r : Γ(gen Z, U.1), DifferentiableOn ℂ (fun b => ev b r) B := fun r b hb =>
      (HolLieFrame.differentiableAt_ev hy (LogKS.chart U) ev
        (fun b' hb' => by rw [hev b' (hm hb')]; exact (spMap_evHom (hm hb')).symm) hb r).differentiableWithinAt
    exact HolFrames.holTan_dualMap hB (F.v ρ i) (fun b hb => evHom (hm hb))
      (fun r => ⟨fun b => ev b r, hd r, fun b hb => (RingHom.congr_fun (hev b (hm hb)) r).symm⟩)
      (fun b hb => hg _ (hm hb) ρ i)
  · obtain ⟨q, h1, h2, h3⟩ := hG U φ F τ k k' hφ
    rw [Set.univ_inter] at h1 h2
    exact ⟨fun j => (h1 j).congr fun v hv => congrArg Complex.re (h3 _ trivial hv.2 _ (hg _ hv.2)),
      fun j => (h2 j).congr fun v hv => congrArg Complex.im (h3 _ trivial hv.2 _ (hg _ hv.2))⟩

end Frames

section Pure

open Matrix Filter Topology GlobalTheory.HermFrame ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FinChart
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ComplexOrder ContDiff

theorem opNorm_chg_le {q : Type} [Fintype q] [DecidableEq q] {K T : Matrix q q ℂ} (hK : K.PosDef) (hT : IsUnit T.det)
    (F : Matrix q q ℂ) : opNorm (Tᵀ * K * Tᴴᵀ) (Tᵀ * K * Tᴴᵀ) (T⁻¹ * F * T) ≤ opNorm K K F := by
  have e : ∀ v, gnorm (Tᵀ * K * Tᴴᵀ) v = gnorm K (T *ᵥ v) := fun v => by
    rw [gnorm, gnorm, form_mulVec, form]
  refine opNorm_le_of_bound (opNorm_nonneg _ _ _) fun v => ?_
  rw [e, e, mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hT, Matrix.one_mul, ← mulVec_mulVec]
  exact gnorm_mulVec_le hK hK.posSemidef _ _

theorem cHess_pull {n e : ℕ} {p : (Fin e → ℂ) → ℝ} {φ : V n → Fin e → ℂ} {f : V n → ℝ} {u : V n} (hφ : AnalyticAt ℂ φ u)
    (hp : ContDiffAt ℝ 2 p (φ u)) (h0 : ∀ w, 0 ≤ levi p (φ u) w) (hf : f =ᶠ[𝓝 u] fun v => p (φ v)) :
    (cHess n (fun v => (f v : ℂ)) u).PosSemidef ∧
      ∀ ξ : V n, gnorm (cHess n (fun v => (f v : ℂ)) u) ξ.ofLp = √(levi p (φ u) (fderiv ℂ φ u ξ)) := by
  let L : (Fin n → ℂ) ≃L[ℂ] V n := (EuclideanSpace.equiv (Fin n) ℂ).symm
  have h2 : ContDiffAt ℝ 2 (fun v => p (φ v)) u := hp.comp u (hφ.contDiffAt.restrict_scalars ℝ)
  have h3 : ContDiffAt ℝ 2 ((fun v => p (φ v)) ∘ toV n) u.ofLp := ContDiffAt.comp _ h2 (toV n).contDiff.contDiffAt
  have e1 : cHess n (fun v => (f v : ℂ)) u = hessC ((fun v => p (φ v)) ∘ toV n) u.ofLp :=
    (ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr (hf.mono fun v hv => congrArg _ hv)).trans (cHess_eq_hessC (z := u.ofLp) h2)
  have hL : AnalyticAt ℂ (φ ∘ L) u.ofLp := AnalyticAt.comp hφ (L.analyticAt _)
  have e2 : ∀ w, levi ((fun v => p (φ v)) ∘ toV n) u.ofLp w = levi p (φ u) (fderiv ℂ φ u (L w)) := fun w => by
    refine (levi_comp w hL hp).trans ?_
    rw [L.comp_right_fderiv]
    rfl
  rw [e1]
  refine ⟨hessC_posSemidef_of_levi _ _ h3 fun w => e2 w ▸ h0 _, fun ξ => ?_⟩
  rw [gnorm, ← leviForm_eq_form_hessC h3, leviForm_self_eq_levi h3, Complex.ofReal_re, e2]
  rfl

theorem opNorm_curv_pull {n e : ℕ} {q : Type} [Fintype q] [DecidableEq q] {K : (Fin e → ℂ) → Matrix q q ℂ}
    {K' T : V n → Matrix q q ℂ} {φ : V n → Fin e → ℂ} {u : V n} (hφ : AnalyticAt ℂ φ u) (hK : MContDiffAt 2 K (φ u))
    (hK0 : (K (φ u)).PosDef) (hT : ∀ a b, AnalyticAt ℂ (fun v => T v a b) u) (hT0 : IsUnit (T u).det)
    (h : K' =ᶠ[𝓝 u] fun v => (T v)ᵀ * K (φ v) * (T v)ᴴᵀ) (ξ η : V n) :
    opNorm (K' u) (K' u) (curv K' u ξ η) ≤
      opNorm (K (φ u)) (K (φ u)) (curv K (φ u) (fderiv ℂ φ u ξ) (fderiv ℂ φ u η)) := by
  have hu : IsUnit (K (φ u)).det := (isUnit_iff_isUnit_det _).1 hK0.isUnit
  have h1 : MContDiffAt 2 (fun v => K (φ v)) u := fun a b => (hK a b).comp u (hφ.contDiffAt.restrict_scalars ℝ)
  have h2 : ∀ᶠ x in 𝓝 u, ∀ η, mdbar T x η = 0 := by
    filter_upwards [eventually_all.2 fun a => eventually_all.2 fun b => (hT a b).eventually_analyticAt] with x hx η
    ext a b
    rw [mdbar_apply, dbar_eq_zero (hx a b).differentiableAt]
    rfl
  rw [curv_congr h, h.self_of_nhds, curv_changeFrame h1 hu (fun a b => (hT a b).contDiffAt.restrict_scalars ℝ) hT0 h2,
    curv_comp_holo hK hu hφ.contDiffAt]
  exact opNorm_chg_le hK0 hT0 _

end Pure

section Charts

open CategoryTheory AlgebraicGeometry Filter Topology ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.M GlobalTheory.CxPts
open scoped ContDiff

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ} {A : FinHolAtlas d (CxPts p σ)}
  {ψ : OpenPartialHomeomorph (CxPts p σ) (Fin d → ℂ)}

theorem isHolTo_compat (hA : IsAlgAtlas A) (hψ : IsCompatChart A ψ) : IsHolTo ψ.target fun z => (ψ.symm z).1 := by
  refine HolPeriods.isHolTo_of_local fun z hz => ?_
  obtain ⟨j, hj⟩ := A.cover (ψ.symm z)
  obtain ⟨c, hc⟩ := hA j
  have h2 := (hψ j).2
  rw [hc] at h2 hj
  refine ⟨ψ.target ∩ ψ.symm ⁻¹' c.finChart.source, ⟨hz, hj⟩, Set.inter_subset_left, ?_⟩
  have h1 := LocLift.isHolTo_comp (TrueCx.TorHolo.isHolTo_symm c) (ψ.isOpen_inter_preimage_symm c.finChart.open_source)
    (β := fun w => (EuclideanSpace.equiv (Fin d) ℂ).symm ((c.finChart ∘ ψ.symm) w))
    ((EuclideanSpace.equiv (Fin d) ℂ).symm.differentiable.comp_differentiableOn h2.differentiableOn)
    fun w hw => c.e.map_source hw.2
  exact LocLift.isHolTo_congr h1 fun w hw => congrArg Subtype.val (c.e.left_inv hw.2).symm

theorem analyticAt_compat (hA : IsAlgAtlas A) (hψ : IsCompatChart A ψ) {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] {B : Set W} (hB : IsOpen B) {y : W → CxPts p σ} (hy : IsHolTo B fun b => (y b).1)
    (hc : ContinuousOn y B) {u : W} (hu : u ∈ B) (hs : y u ∈ ψ.source) : AnalyticAt ℂ (fun v => ψ (y v)) u := by
  obtain ⟨j, hj⟩ := A.cover (y u)
  obtain ⟨c, hc'⟩ := hA j
  have h2 := (hψ j).1
  rw [hc'] at h2 hj
  have hO := hc.isOpen_inter_preimage hB c.finChart.open_source
  have h1 : AnalyticAt ℂ (fun v => c.finChart (y v)) u := SCV.analyticOnNhd_of_differentiableOn hO (fun v hv =>
    ((EuclideanSpace.equiv (Fin d) ℂ).differentiableAt.comp v
      (TrueCx.TorHolo.differentiableAt_chart hB hy c hv.1 hv.2)).differentiableWithinAt) u ⟨hu, hj⟩
  refine (AnalyticAt.comp (f := fun v => c.finChart (y v)) (h2 _ ⟨c.finChart.map_source hj,
    by rwa [Set.mem_preimage, c.finChart.left_inv hj]⟩) h1).congr ?_
  filter_upwards [hO.mem_nhds ⟨hu, hj⟩] with v hv
  exact congrArg ψ (c.finChart.left_inv hv.2)

end Charts

section Dual

open Matrix Filter Topology GlobalTheory.HermFrame GlobalTheory.CurvInterp
open scoped ComplexOrder ContDiff

theorem dualRev_dualRev {q : ℕ} {M : Matrix (Fin q) (Fin q) ℂ} (hM : M.PosDef) : dualRev (dualRev M) = M := by
  have e : ∀ N : Matrix (Fin q) (Fin q) ℂ, dualRev N = (N⁻¹ᵀ).submatrix Fin.revPerm Fin.revPerm := fun _ => rfl
  rw [e, e, inv_submatrix_equiv, transpose_submatrix, ← transpose_nonsing_inv, transpose_transpose,
    nonsing_inv_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hM.isUnit)]
  ext a b
  simp

theorem bound_congr {e : ℕ} {q : Type} [Fintype q] [DecidableEq q] {U : Set (Fin e → ℂ)}
    {K K' : (Fin e → ℂ) → Matrix q q ℂ} {G : (Fin e → ℂ) → Matrix (Fin e) (Fin e) ℂ} {C : ℝ} (h : IsPosFrame U K)
    (hb : TwoFormBound U K G (curv K) C) (he : ∀ z ∈ U, K' z = K z) {z : Fin e → ℂ} (hz : z ∈ U) :
    MContDiffAt 2 K' z ∧ ∀ ξ η, opNorm (K' z) (K' z) (curv K' z ξ η) ≤ C * gnorm (G z) ξ * gnorm (G z) η := by
  have h1 : K' =ᶠ[𝓝 z] K := mem_of_superset (h.isOpen.mem_nhds hz) he
  refine ⟨fun a b => (h.isHermFrame.two hz a b).congr_of_eventuallyEq (h1.mono fun v hv => by simp only [hv]), fun ξ η => ?_⟩
  rw [curv_congr h1, he z hz]
  exact (hb z hz).2.2 ξ η

end Dual

section Local

open CategoryTheory AlgebraicGeometry Filter Topology Matrix NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CxPts GlobalTheory.HermFrame GlobalTheory.CurvInterp GlobalTheory.IndefiniteRowSideFullHecke.HermitianInterpolation GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms GlobalTheory.GradedNorm
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {s : FinalTheorems S κ}

theorem interp_gram_or (x : ToroidalCompactificationData s) {σ : κ.c.F →+* ℂ} (τ : D.host.E →+* ℂ) :
    (∀ (R : ℝ) (y : CxPts (genStr s.T.Z) σ) (g : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)),
      ((x.eigMetAt σ (some R)).gram y g τ)ᵀ = ((1 - x.wt σ R y : ℝ) : ℂ) • ((x.eigMet σ).gram y g τ)ᵀ +
        (x.wt σ R y : ℂ) • ((x.hodge σ).gram y g τ)ᵀ) ∨
    ∀ (R : ℝ) (y : CxPts (genStr s.T.Z) σ) (g : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)),
      ((x.eigMetAt σ (some R)).gram y g τ)ᵀ = dualRev (((1 - x.wt σ R y : ℝ) : ℂ) • dualRev ((x.eigMet σ).gram y g τ)ᵀ +
        (x.wt σ R y : ℂ) • dualRev ((x.hodge σ).gram y g τ)ᵀ) := by
  by_cases h : τ (A.H.rt : D.host.E) = A.H.rt0
  · refine .inl fun R y g => ?_
    rw [ToroidalCompactificationData.eigMetAt, EigMet.interp_gram _ h, mix, transpose_add, transpose_smul, transpose_smul]
  · refine .inr fun R y g => (dualRev_dualRev ((x.eigMetAt σ (some R)).pos y g τ).transpose).symm.trans (congrArg _ ?_)
    have e := EigMet.dualGram_interp_gram (hs := x.wt_mem R) (G₀ := x.eigMet σ) (G := x.hodge σ) g h
    have e2 : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ), dualRev Mᵀ = (GlobalTheory.LieMet.dualGram M)ᵀ.submatrix Fin.rev Fin.rev :=
      fun M => by rw [dualRev, GlobalTheory.HermFrame.dualGram, GlobalTheory.LieMet.dualGram, ← transpose_nonsing_inv]
    rw [ToroidalCompactificationData.eigMetAt, e2, e, e2, e2, mix, transpose_add, transpose_smul, transpose_smul]
    rfl

theorem exists_model_bound (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ) [CompactSpace (CxPts (genStr s.T.Z) σ)]
    {α : LocPot (CxPts (genStr s.T.Z) σ)} {Λ : Fin x.m → LocPot (CxPts (genStr s.T.Z) σ)}
    {sg : Fin x.m → CxPts (genStr s.T.Z) σ → CxPts (genStr s.T.Z) σ → ℂ} {t Cg Cm ρ₁ : ℝ}
    (hB : IsBoundary (manifold s.T.Z σ).finAtlas Λ sg fun i => {y | LiesIn y (x.cpt i)})
    (hn : ∀ i y, normSec (Λ i) (sg i) y = x.nrm σ i y) (hS : ScalarBounds Λ sg fun i => {y | LiesIn y (x.cpt i)})
    (hCg : 0 < Cg) (hG : GrowthBounds (manifold s.T.Z σ).finAtlas α Λ sg (fun i => {y | LiesIn y (x.cpt i)}) t Cg)
    {ψ : OpenPartialHomeomorph (CxPts (genStr s.T.Z) σ) (Fin S.Dw.dim → ℂ)} {σ' : Fin x.m → Option (Fin S.Dw.dim)}
    (hψ : IsAdaptedPolydisc (manifold s.T.Z σ).finAtlas (fun i => {y | LiesIn y (x.cpt i)}) ψ σ') (hρ₁ : 0 < ρ₁)
    (hρ₁1 : ρ₁ ≤ 1) (hfm : ∀ z ∈ Metric.ball (0 : Fin S.Dw.dim → ℂ) ρ₁, ψ.symm z ∉ ⋃ i, {y | LiesIn y (x.cpt i)} →
      ∀ w, formAt ψ (poincarePot α Λ sg t) z w ≤ Cm * modelAt σ' z w)
    {g : ∀ y : CxPts (genStr s.T.Z) σ, EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)}
    (hHol : HolFam (Metric.ball 0 ρ₁) fun z => ⟨ψ.symm z, g (ψ.symm z)⟩)
    (hsm : ∀ τ, IsPosFrame (Metric.ball 0 ρ₁) fun z => ((x.eigMet σ).gram (ψ.symm z) (g (ψ.symm z)) τ)ᵀ) :
    ∃ ρ C : ℝ, 0 < ρ ∧ ρ ≤ ρ₁ ∧ 0 ≤ C ∧ ∀ R : ℝ, 2 ≤ R → ∀ τ, ∀ z ∈ Metric.ball (0 : Fin S.Dw.dim → ℂ) ρ, Inner (ψ.symm z) →
      MContDiffAt 2 (fun v => ((x.eigMetAt σ (some R)).gram (ψ.symm v) (g (ψ.symm v)) τ)ᵀ) z ∧ ∀ ξ η,
        opNorm ((x.eigMetAt σ (some R)).gram (ψ.symm z) (g (ψ.symm z)) τ)ᵀ
          ((x.eigMetAt σ (some R)).gram (ψ.symm z) (g (ψ.symm z)) τ)ᵀ
          (curv (fun v => ((x.eigMetAt σ (some R)).gram (ψ.symm v) (g (ψ.symm v)) τ)ᵀ) z ξ η) ≤
          C * √(modelAt σ' z ξ) * √(modelAt σ' z η) := by
  have hb₁ : Metric.ball (0 : Fin S.Dw.dim → ℂ) ρ₁ ⊆ ψ.target := (Metric.ball_subset_ball hρ₁1).trans hψ.2.1
  have hI : ∀ y : CxPts (genStr s.T.Z) σ, Inner y ↔ y ∉ ⋃ i, {y | LiesIn y (x.cpt i)} := fun y =>
    ((x.liesIn_genBd_iff y).trans (Set.mem_iUnion (s := fun i => {y | LiesIn y (x.cpt i)}) (x := y)).symm).not
  have hrx : ∀ y, rTot Λ sg y = x.r σ y := fun y => by simp only [rTot, hn, OddPrimesWithRootsOfUnity.r]
  obtain ⟨ρ, hρ, hb, hblk⟩ := hodgeLocal x σ _ _ _ Metric.isOpen_ball (Metric.mem_ball_self hρ₁) hHol
    (ψ.continuousOn_symm.mono hb₁)
  wlog hρρ : ρ ≤ ρ₁ generalizing ρ
  · exact this ρ₁ hρ₁ (Set.Subset.refl _) (hblk.mono (not_le.1 hρρ).le) le_rfl
  have hρ1 : ρ ≤ 1 := hρρ.trans hρ₁1
  have hpz : ∀ {ρ' : ℝ}, ρ' ≤ 1 → ∀ z ∈ Metric.ball (0 : Fin S.Dw.dim → ℂ) ρ', (Inner (ψ.symm z) ↔ z ∈ punct σ' ρ') :=
    fun h1 z hz => by
      have := hψ.2.2.2 z (Metric.ball_subset_ball h1 hz)
      simp only [hI, Set.mem_iUnion, this, punct, Set.mem_setOf_eq, hz, true_and, not_exists, not_and, ne_eq]
  have hpZ : ∀ z ∈ punct σ' ρ, Inner (ψ.symm z) := fun z hz => (hpz hρ1 z hz.1).2 hz
  have hpt : ∀ z ∈ punct σ' ρ, z ∈ ψ.target := fun z hz => hb₁ (hb hz.1)
  have hpD := fun z hz => (hI _).1 (hpZ z hz)
  have hrs : ContDiffOn ℝ ∞ (rTot Λ sg ∘ ψ.symm) (punct σ' ρ) := by
    refine ContDiffOn.congr (f := fun z => ∑ i, (rComp Λ sg i ∘ ψ.symm) z - ((x.m : ℝ) - 1) * Real.exp 1) (fun z hz => ?_)
      fun z hz => (hS _ (hpD z hz)).2.1
    exact ((ContDiffAt.sum fun i _ => GlobalTheory.T.boundary_potential_smooth_off_divisor _ Λ sg _ hB i ψ hψ.1 z (hpt z hz)
      fun h => hpD z hz (Set.mem_iUnion.2 ⟨i, h⟩)).sub contDiffAt_const).contDiffWithinAt
  have hre : ∀ z ∈ punct σ' ρ, Real.exp 1 ≤ (rTot Λ sg ∘ ψ.symm) z := fun z _ => by
    rw [Function.comp_apply, hrx]; exact x.exp_le_r _ _
  have hr2 : ∀ z ∈ punct σ' ρ, ContDiffAt ℝ 2 (rTot Λ sg ∘ ψ.symm) z := fun z hz =>
    (hrs.contDiffAt ((isOpen_punct σ' ρ).mem_nhds hz)).of_le (WithTop.coe_le_coe.2 le_top)
  obtain ⟨-, hmu⟩ := x.isMuExp_muExp (ToroidalCompactificationData.exists_isMuExp x)
  obtain ⟨ρ', C, hρ', hρ'ρ, hdat⟩ := exists_isData σ' (Cμ := x.muExp) (CP := Cg * Cm / 2)
    (H₀ := fun τ z => ((x.eigMet σ).gram (ψ.symm z) (g (ψ.symm z)) τ)ᵀ) hρ hρ1 hpZ hblk
    (fun τ => isPosFrame_mono (hsm τ) Metric.isOpen_ball hb) hrs hre
    (fun τ z hz v => by
      simp only [form_transpose_self, Function.comp_apply, hrx]
      exact hmu _ _ (hpZ z hz) (g _) τ v)
    (fun z hz ξ => by
      have h1 := (hG ψ hψ.1 z (hpt z hz) (hpD z hz) ξ).1
      have h2 := mul_le_mul_of_nonneg_left (hfm z (hb hz.1) (hpD z hz) ξ) hCg.le
      rw [diagVal_gradForm ((hr2 z hz).differentiableAt two_ne_zero)]
      have e : diagVal (fun ξ η => ((Cg * Cm / 2 : ℝ) : ℂ) * formOf (modelGram σ' z) ξ η) ξ =
          Cg * Cm / 2 * modelAt σ' z ξ := by
        rw [← form_modelGram, ← diagVal_formOf, diagVal, diagVal, mul_left_comm, Complex.re_ofReal_mul]
      rw [e]
      simp only [gradSqAt] at h1
      simp only [Function.comp_apply]
      linarith)
    (fun z hz => formAbsLe_iff.2 fun ξ => by
      have h1 := (hG ψ hψ.1 z (hpt z hz) (hpD z hz) ξ).2.1
      have h2 := mul_le_mul_of_nonneg_left (hfm z (hb hz.1) (hpD z hz) ξ) hCg.le
      rw [diagVal_ddc ((hr2 z hz).log ((Real.exp_pos 1).trans_le (hre z hz)).ne'), diagVal_formOf, form_modelGram]
      have e : levi (fun v => Real.log ((rTot Λ sg ∘ ψ.symm) v)) z ξ / (2 * Real.pi) =
          ddcAt ψ (fun y => Real.log (rTot Λ sg y)) z ξ / 2 := by
        rw [ddcAt]; field_simp; rfl
      rw [e, abs_div, abs_two]
      linarith)
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.T.interpolation_curvature_bound x.muExp C C C (Cg * Cm / 2) x.kap _ x.lt_kap isCutoff_sq
  refine ⟨ρ', max C₁ 0, hρ', hρ'ρ.trans hρρ, le_max_right _ _, fun R hR τ z hz hzI => ?_⟩
  have hz' := (hpz (hρ'ρ.trans hρ1) z hz).1 hzI
  have hs : IsWeight _ x.kap (rTot Λ sg ∘ ψ.symm) fun v =>
      1 * cutWeight (fun y => Real.smoothTransition (3 - y) ^ 2) x.kap R (rTot Λ sg ∘ ψ.symm) v :=
    Or.inr ⟨1, ⟨zero_le_one, le_rfl⟩, R, hR, rfl⟩
  have hw : ∀ v ∈ punct σ' ρ', x.wt σ R (ψ.symm v) =
      1 * cutWeight (fun y => Real.smoothTransition (3 - y) ^ 2) x.kap R (rTot Λ sg ∘ ψ.symm) v := fun v hv => by
    rw [x.wt_eq hR (hpZ v (punct_mono σ' hρ'ρ hv)), one_mul, ← hrx]; rfl
  simp only [← form_modelGram]
  rcases interp_gram_or x (σ := σ) τ with h | h
  · have a := (hC₁ _ _ _ _ _ _ _ (hdat τ).1).1 _ hs
    exact bound_congr a.1 (a.2.1.mono (le_max_left _ _)) (fun v hv => by rw [h, hw v hv]; rfl) hz'
  · have a := (hC₁ _ _ _ _ _ _ _ (hdat τ).2).1 _ hs
    have b := GlobalTheory.T.one_form_bound_connection_transfer _ _ _ _ a.1
    exact bound_congr b.1 ((b.2.2.1 _ _ a.2.1).mono (le_max_left _ _)) (fun v hv => by rw [h, hw v hv]; rfl) hz'

end Local

section Pot

open Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms GlobalTheory.CurvInterp
open scoped ContDiff

variable {e m : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {α : LocPot X} {Λ : Fin m → LocPot X}
  {sg : Fin m → X → X → ℂ} {D : Fin m → Set X} {t : ℝ} {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} {y : X}

theorem levi_nonneg_compat (hα : IsPotential A α) (hαp : IsPosPot A α) (hψ : IsCompatChart A ψ) (hy : y ∈ ψ.source)
    (w : Fin e → ℂ) : 0 ≤ levi (α.φ y ∘ ψ.symm) (ψ y) w := by
  have hl := ψ.left_inv hy
  obtain ⟨k, hk⟩ := A.cover y
  have hk' := (A.chart k).left_inv hk
  have hm : ψ y ∈ ψ.target ∩ ψ.symm ⁻¹' (A.chart k).source := ⟨ψ.map_source hy, by rwa [Set.mem_preimage, hl]⟩
  have hK := contDiffAt_two_compat (isCompatChart_chart A k) (α.isOpen_U y) (hα.1 y) ((A.chart k).map_source hk)
    (by rw [hk']; exact α.mem_U y)
  have hev : (α.φ y ∘ ψ.symm) =ᶠ[𝓝 (ψ y)] ((α.φ y ∘ (A.chart k).symm) ∘ (A.chart k ∘ ψ.symm)) := by
    filter_upwards [(ψ.isOpen_inter_preimage_symm (A.chart k).open_source).mem_nhds hm] with u hu
    exact congrArg (α.φ y) ((A.chart k).left_inv hu.2).symm
  rw [levi_congr hev, levi_comp w ((hψ k).2 _ hm) (by rwa [Function.comp_apply, hl]), Function.comp_apply, hl]
  generalize fderiv ℂ (A.chart k ∘ ψ.symm) (ψ y) w = w'
  by_cases hw : w' = 0
  · rw [hw, levi_zero]
  · exact (hαp _ k _ ⟨(A.chart k).map_source hk, by rw [Set.mem_preimage, hk']; exact α.mem_U y⟩ w' hw).le

theorem levi_poincarePot_nonneg (hα : IsPotential A α) (hαp : IsPosPot A α) (hB : IsBoundary A Λ sg D) (ht : 0 < t)
    (hS : ScalarBounds Λ sg D) (hT : TwoSided A α Λ sg D t) (hψ : IsCompatChart A ψ) (hy : y ∈ ψ.source)
    (hD : y ∉ ⋃ i, D i) : ContDiffAt ℝ 2 ((poincarePot α Λ sg t).φ y ∘ ψ.symm) (ψ y) ∧
      ∀ w, 0 ≤ levi ((poincarePot α Λ sg t).φ y ∘ ψ.symm) (ψ y) w := by
  have hl := ψ.left_inv hy
  have hπ := Real.pi_pos
  have hK := contDiffAt_two_compat hψ (α.isOpen_U y) (hα.1 y) (ψ.map_source hy) (by rw [hl]; exact α.mem_U y)
  refine ⟨hK.add (contDiffAt_const.mul (ContDiffAt.sum fun i _ => ?_)), fun w => ?_⟩
  · exact ((GlobalTheory.T.boundary_potential_smooth_off_divisor _ Λ sg _ hB i ψ hψ _ (ψ.map_source hy) fun h =>
      hD (Set.mem_iUnion.2 ⟨i, hl ▸ h⟩)).of_le (WithTop.coe_le_coe.2 le_top)).log
      ((Real.exp_pos 1).trans_le ((hS _ (hl.symm ▸ hD)).1 i)).ne'
  · have h1 := (hT ψ hψ _ (ψ.map_source hy) (hl.symm ▸ hD) w).1
    have h2 := levi_nonneg_compat hα hαp hψ hy w
    have h3 : 0 ≤ t * ∑ i, gradSqAt ψ (rComp Λ sg i) (ψ y) w / rComp Λ sg i (ψ.symm (ψ y)) ^ 2 :=
      mul_nonneg ht.le (Finset.sum_nonneg fun i _ => div_nonneg (gradSqAt_nonneg _ _ _ _) (sq_nonneg _))
    have h4 : 0 ≤ formAt ψ α (ψ y) w := by
      rw [formAt, hl]; positivity
    have h5 : 0 ≤ formAt ψ (poincarePot α Λ sg t) (ψ y) w := by linarith
    rw [formAt, hl] at h5
    exact nonneg_of_mul_nonneg_right h5 (by positivity)

end Pot

section Main

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.CovTest GlobalTheory.VdmRec GlobalTheory.ArchLim
open GlobalTheory.MixDens (part IsDens chernMat emb)
open GlobalTheory.FlagFibre (Low uni)
open ReciprocityTheory.L2DbarEstimates (V cHess bas)
open ReciprocityTheory.AnForm.M (LocPot FinHolAtlas IsPotential IsSection)
open GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions (IsProjective IsIrreducibleAnalytic IsIrreducibleComponent regularLocus regIntegral normSec absLogNorm boundary rFun poincarePot IsBoundarySetting)
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Hor GlobalTheory.Mean4O
open scoped ContDiff ComplexOrder ENNReal Classical

set_option maxHeartbeats 800000 in

theorem exists_curvBound : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ) [CompactSpace (CxPts (genStr s.T.Z) σ)] (α : LocPot (CxPts (genStr s.T.Z) σ)) (Λ : Fin x.m → LocPot (CxPts (genStr s.T.Z) σ)) (sg : Fin x.m → CxPts (genStr s.T.Z) σ → CxPts (genStr s.T.Z) σ → ℂ) (t : ℝ), IsPotential (manifold s.T.Z σ).finAtlas α → ReciprocityTheory.AnForm.M.IsPosPot (manifold s.T.Z σ).finAtlas α → GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.IsBoundary (manifold s.T.Z σ).finAtlas Λ sg (fun i => {y | LiesIn y (x.cpt i)}) → (∀ i y, GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.normSec (Λ i) (sg i) y = x.nrm σ i y) → 0 < t → GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.ScalarBounds Λ sg (fun i => {y | LiesIn y (x.cpt i)}) → GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.IsPotentialOn (manifold s.T.Z σ).finAtlas (⋃ i, {y | LiesIn y (x.cpt i)})ᶜ (GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.poincarePot α Λ sg t) → GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.TwoSided (manifold s.T.Z σ).finAtlas α Λ sg (fun i => {y | LiesIn y (x.cpt i)}) t → (∃ C : ℝ, 0 < C ∧ GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.GrowthBounds (manifold s.T.Z σ).finAtlas α Λ sg (fun i => {y | LiesIn y (x.cpt i)}) t C) → (∀ (ψ : OpenPartialHomeomorph (CxPts (genStr s.T.Z) σ) (Fin S.Dw.dim → ℂ)) (σ' : Fin x.m → Option (Fin S.Dw.dim)), GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.IsAdaptedPolydisc (manifold s.T.Z σ).finAtlas (fun i => {y | LiesIn y (x.cpt i)}) ψ σ' → ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 / 2 ∧ (∃ C : ℝ, 0 < C ∧ ∀ z ∈ Metric.ball (0 : Fin S.Dw.dim → ℂ) ρ, ψ.symm z ∉ ⋃ i, {y | LiesIn y (x.cpt i)} → C⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.tSum σ' z ≤ GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.rTot Λ sg (ψ.symm z) ∧ GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.rTot Λ sg (ψ.symm z) ≤ C * GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.tSum σ' z) ∧ ∃ C : ℝ, 0 < C ∧ ∀ z ∈ Metric.ball (0 : Fin S.Dw.dim → ℂ) ρ, ψ.symm z ∉ ⋃ i, {y | LiesIn y (x.cpt i)} → ∀ w, C⁻¹ * GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.modelAt σ' z w ≤ GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.formAt ψ (GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.poincarePot α Λ sg t) z w ∧ GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.formAt ψ (GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.poincarePot α Λ sg t) z w ≤ C * GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.modelAt σ' z w) → ∃ C : ℝ, CurvBound x σ (poincarePot α Λ sg t) C := by
  intro D A N j S κ s x σ _ α Λ sg t hα hαp hB hn ht hS _ hT ⟨Cg, hCg, hG⟩ hmod
  have hA := (manifold s.T.Z σ).isAlgAtlas_finAtlas
  have hπ := Real.pi_pos
  have hP : poincarePot α Λ sg t = GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.poincarePot α Λ sg t := by
    refine congrArg (fun f => α + LocPot.ofFun f) (funext fun y => ?_)
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions.pFun, rFun, GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.rComp_eq]
    ring
  have hI : ∀ y : CxPts (genStr s.T.Z) σ, Inner y ↔ y ∉ ⋃ i, {y | LiesIn y (x.cpt i)} := fun y =>
    ((x.liesIn_genBd_iff y).trans (Set.mem_iUnion (s := fun i => {y | LiesIn y (x.cpt i)}) (x := y)).symm).not
  rw [hP]
  set P := GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.poincarePot α Λ sg t with hPdef
  have hpot := fun ψ hψ y hy hyI => levi_poincarePot_nonneg hα hαp hB ht hS hT (ψ := ψ) hψ (y := y) hy ((hI y).1 hyI)

  have hloc : ∀ y₀ : CxPts (genStr s.T.Z) σ, ∃ (O : Set (CxPts (genStr s.T.Z) σ)) (C : ℝ), IsOpen O ∧ y₀ ∈ O ∧
      ∀ (n : ℕ) (U : Set (V n)) (a : V n → CxFr s.T.Z σ), IsOpen U → HolFam U a → ContinuousOn (fun u => (a u).1) U →
      ∀ u ∈ U, Inner (a u).1 → (a u).1 ∈ O → (cHess n (fun v => (P.φ (a u).1 (a v).1 : ℂ)) u).PosSemidef ∧
      ∀ R : ℝ, 2 ≤ R → ∀ (τ : D.host.E →+* ℂ) (ξ η : V n),
        opNorm (eigGram (x.eigMetAt σ (some R)) a τ u) (eigGram (x.eigMetAt σ (some R)) a τ u)
          (curv (eigGram (x.eigMetAt σ (some R)) a τ) u ξ η) ≤
          C * gnorm (cHess n (fun v => (P.φ (a u).1 (a v).1 : ℂ)) u) ξ.ofLp *
            gnorm (cHess n (fun v => (P.φ (a u).1 (a v).1 : ℂ)) u) η.ofLp := by
    intro y₀
    obtain ⟨ψ, σ', hψ, hy₀, h0⟩ := GlobalTheory.T.adapted_polydisc_exists_at _ Λ sg _ hB y₀
    obtain ⟨ρP, hρP, hρP2, -, Cm, hCm, hfm⟩ := hmod ψ σ' hψ
    obtain ⟨W, g, hW, hyW, hgh, hgs⟩ := exists_frames y₀
    obtain ⟨ρ₀, hρ₀, hb₀⟩ := Metric.isOpen_iff.1 (ψ.isOpen_inter_preimage_symm hW) 0
      (h0 ▸ ⟨ψ.map_source hy₀, by rwa [Set.mem_preimage, ψ.left_inv hy₀]⟩)
    have s0 := (Metric.ball_subset_ball (x := (0 : Fin S.Dw.dim → ℂ)) (min_le_left ρ₀ ρP)).trans hb₀
    have sP := Metric.ball_subset_ball (x := (0 : Fin S.Dw.dim → ℂ)) (min_le_right ρ₀ ρP)
    obtain ⟨ρ, C, hρ, hρ₁, hC, hb⟩ := exists_model_bound x σ hB hn hS hCg hG hψ (lt_min hρ₀ hρP)
      ((min_le_right _ _).trans (hρP2.trans (by norm_num))) (fun z hz h w => (hfm z (sP hz) h w).2) (g := g)
      (hgh _ _ _ Metric.isOpen_ball
        (LocLift.isHolTo_mono (isHolTo_compat hA hψ.1) Metric.isOpen_ball fun z hz => (s0 hz).1) fun z hz => (s0 hz).2)
      fun τ => ⟨Metric.isOpen_ball, fun k k' => by
        obtain ⟨h1, h2⟩ := hgs _ (x.smoothOn_eigMet σ) τ k' k
        have h1' := (ReciprocityTheory.AnForm.M.PLAux.contDiffOn_compat hψ.1 hW ((hA.smoothOn_iff _ hW).2 h1)).mono s0
        have h2' := (ReciprocityTheory.AnForm.M.PLAux.contDiffOn_compat hψ.1 hW ((hA.smoothOn_iff _ hW).2 h2)).mono s0
        exact ((Complex.ofRealCLM.contDiff.comp_contDiffOn h1').add ((Complex.ofRealCLM.contDiff.comp_contDiffOn h2').mul
          (contDiffOn_const (c := Complex.I)))).congr fun z _ => (Complex.re_add_im _).symm,
        fun z _ => ((x.eigMet σ).pos _ _ τ).transpose⟩
    have s1 := Metric.ball_subset_ball (x := (0 : Fin S.Dw.dim → ℂ)) hρ₁
    have hO := ψ.isOpen_inter_preimage (Metric.isOpen_ball (x := (0 : Fin S.Dw.dim → ℂ)) (ε := ρ))
    refine ⟨_, C * (Cm * (2 / Real.pi)), hO, ⟨hy₀, by simpa [h0] using hρ⟩, fun n U a hU ha hc u hu huI huO => ?_⟩
    have hl := ψ.left_inv huO.1
    have hφ := analyticAt_compat hA hψ.1 hU ha.1 hc hu huO.1
    have hU' := hc.isOpen_inter_preimage hU hO
    have hn' := hU'.mem_nhds ⟨hu, huO⟩
    obtain ⟨p2, p0⟩ := hpot ψ hψ.1 _ huO.1 huI
    obtain ⟨q1, q2⟩ := cHess_pull (f := fun v => P.φ (a u).1 (a v).1) hφ p2 p0
      (mem_of_superset hn' fun v hv => congrArg (P.φ (a u).1) (ψ.left_inv hv.2.1).symm)
    refine ⟨q1, fun R hR τ ξ η => ?_⟩
    obtain ⟨k2, kb⟩ := hb R hR τ _ huO.2 (hl.symm ▸ huI)
    have ha' : HolFam (U ∩ (fun u => (a u).1) ⁻¹' (ψ.source ∩ ψ ⁻¹' Metric.ball 0 ρ)) a :=
      ⟨LocLift.isHolTo_mono ha.1 hU' Set.inter_subset_left,
        fun τ i U f => (ha.2 τ i U f).mono fun z hz => ⟨hz.1.1, hz.2⟩⟩
    have hg' := hgh _ _ (fun u => (a u).1) hU' ha'.1 fun v hv => ψ.left_inv hv.2.1 ▸ (s0 (s1 hv.2.2)).2
    have key := opNorm_curv_pull (K' := eigGram (x.eigMetAt σ (some R)) a τ) (T := fun v => (g (a v).1).co (a v).2 τ) hφ k2
      ((x.eigMetAt σ (some R)).pos _ _ τ).transpose
      (fun k i => SCV.analyticOnNhd_of_differentiableOn hU'
        (fun v hv => (differentiableAt_co hg' ha' τ k i hv).differentiableWithinAt) u ⟨hu, huO⟩)
      (EigFrame.isUnit_det_co _ _ _) (mem_of_superset hn' fun v hv => by
        have e := congrArg (fun y => ((x.eigMetAt σ (some R)).gram y (g y) τ)ᵀ) (ψ.left_inv hv.2.1)
        simp only [Set.mem_setOf_eq] at e ⊢
        rw [e, eigGram, (x.eigMetAt σ (some R)).change _ (g (a v).1), transpose_mul, transpose_mul, Matrix.mul_assoc]) ξ η
    have hm : ∀ w, √(GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.modelAt σ' (ψ (a u).1) w) ≤
        √(Cm * (2 / Real.pi)) * √(ReciprocityTheory.AnForm.levi (P.φ (a u).1 ∘ ψ.symm) (ψ (a u).1) w) := fun w => by
      have h := (hfm _ (sP (s1 huO.2)) (hl.symm ▸ (hI _).1 huI) w).1
      rw [inv_mul_le_iff₀ hCm, GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms.formAt, hl, ← _root_.mul_assoc] at h
      rw [← Real.sqrt_mul (by positivity)]
      exact Real.sqrt_le_sqrt h
    rw [q2, q2]
    refine (key.trans (kb _ _)).trans ((mul_le_mul (mul_le_mul_of_nonneg_left (hm _) hC) (hm _) (Real.sqrt_nonneg _)
      (by positivity)).trans_eq ?_)
    have e := Real.mul_self_sqrt (x := Cm * (2 / Real.pi)) (by positivity)
    linear_combination (C * √(ReciprocityTheory.AnForm.levi (P.φ (a u).1 ∘ ψ.symm) (ψ (a u).1) (fderiv ℂ (fun v => ψ (a v).1) u ξ)) *
      √(ReciprocityTheory.AnForm.levi (P.φ (a u).1 ∘ ψ.symm) (ψ (a u).1) (fderiv ℂ (fun v => ψ (a v).1) u η))) * e
  choose O C hO hy hb using hloc
  obtain ⟨F, hF⟩ := isCompact_univ.elim_finite_subcover O hO fun y _ => Set.mem_iUnion.2 ⟨y, hy y⟩
  refine ⟨∑ y ∈ F, |C y|, fun n U a hU ha hc u hu huI => ?_⟩
  obtain ⟨y₀, hy₀, huO⟩ := Set.mem_iUnion₂.1 (hF (Set.mem_univ (a u).1))
  obtain ⟨h1, h2⟩ := hb y₀ n U a hU ha hc u hu huI huO
  refine ⟨h1, fun R hR τ ξ η => (h2 R hR τ ξ η).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun y => |C y|) (fun _ _ => abs_nonneg _) hy₀)) (gnorm_nonneg _ _)) (gnorm_nonneg _ _)

end Main

end GlobalTheory.ArchLim.CurvFam
