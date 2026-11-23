import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatiosEqOfSameOrbit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HolomorphicLiftGivesHolomorphicSection
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictChernPart
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ.ArchEq.Dens

section Change

open Set

variable {k : Type} [CommRing k] {Y : Scheme.{0}} {q : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ} {B : LB Y}

theorem restrict_chernPart_of_coords [SecondCountableTopology (GlobalTheory.CxPts q σ)] {φ : GlobalTheory.Weight q σ B} (h : φ.IsCInf)
    (ε : ℤˣ) (c : GlobalTheory.AlgChart q σ D) (e : OpenPartialHomeomorph (GlobalTheory.CxPts q σ) (Fin D → ℂ))
    (hsub : e.source ⊆ c.e.source) (hd : DifferentiableOn ℂ (c.finChart ∘ e.symm) e.target) {ρ : (Fin D → ℂ) → ℝ}
    (hρ : ∀ v ∈ e.target, ρ v = ‖LinearMap.det (fderiv ℂ (c.finChart ∘ e.symm) v :
      (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))‖ ^ 2 * c.chernDens φ (e.symm v)) :
    (φ.chernPart D ε).restrict e.source =
      ((volume.restrict e.target).withDensity fun v => ENNReal.ofReal (((ε : ℤ) : ℝ) * ρ v)).map e.symm := by
  ext T hT
  set κ := c.finChart ∘ e.symm with hκ
  have ht := e.open_target.measurableSet
  have hs : AEMeasurable e.symm (volume.restrict e.target) := e.continuousOn_symm.aemeasurable ht
  have hS : MeasurableSet (T ∩ e.source) := hT.inter e.open_source.measurableSet
  have hSc : T ∩ e.source ⊆ c.finChart.source := inter_subset_right.trans hsub
  have hA : MeasurableSet (e.target ∩ e.symm ⁻¹' T) := by
    have hm : Measurable (e.target.restrict e.symm) :=
      (continuousOn_iff_continuous_restrict.1 e.continuousOn_symm).measurable
    have := ht.subtype_image (hm hT)
    convert this using 1
    ext v
    exact ⟨fun hv => ⟨⟨v, hv.1⟩, hv.2, rfl⟩, by rintro ⟨w, hw, rfl⟩; exact ⟨w.2, hw⟩⟩
  have him : c.finChart.target ∩ c.finChart.symm ⁻¹' (T ∩ e.source) = κ '' (e.target ∩ e.symm ⁻¹' T) := by
    rw [← c.finChart.image_source_inter_eq', inter_eq_right.2 hSc]
    ext z
    constructor
    · rintro ⟨y, ⟨hyT, hys⟩, rfl⟩
      exact ⟨e y, ⟨e.map_source hys, by simpa only [mem_preimage, e.left_inv hys] using hyT⟩, by
        simp only [hκ, Function.comp_apply, e.left_inv hys]⟩
    · rintro ⟨v, ⟨hv, hvT⟩, rfl⟩
      exact ⟨e.symm v, ⟨hvT, e.map_target hv⟩, rfl⟩
  have hinj : InjOn κ (e.target ∩ e.symm ⁻¹' T) := fun v hv w hw hvw => by
    have h1 := c.finChart.injOn (hsub (e.map_target hv.1)) (hsub (e.map_target hw.1)) hvw
    exact e.symm.injOn hv.1 hw.1 h1
  have hder : ∀ v ∈ e.target ∩ e.symm ⁻¹' T, HasFDerivWithinAt κ
      ((fderiv ℂ κ v).restrictScalars ℝ) (e.target ∩ e.symm ⁻¹' T) v := fun v hv =>
    (((hd.differentiableAt (e.open_target.mem_nhds hv.1)).hasFDerivAt).restrictScalars ℝ).hasFDerivWithinAt
  have hsc : AEMeasurable c.finChart.symm (volume.restrict c.finChart.target) :=
    c.finChart.continuousOn_symm.aemeasurable c.finChart.open_target.measurableSet
  have e1 : φ.chernPart D ε (T ∩ e.source) =
      ((φ.chernPart D ε).restrict c.finChart.source) (T ∩ e.source) := by
    rw [Measure.restrict_apply hS, inter_eq_left.2 hSc]
  rw [Measure.restrict_apply hT, e1, GlobalTheory.ChernMA.restrict_chernPart h ε c,
    Measure.map_apply_of_aemeasurable (hsc.mono_ac (withDensity_absolutelyContinuous _ _)) hS,
    Measure.map_apply_of_aemeasurable (hs.mono_ac (withDensity_absolutelyContinuous _ _)) hT,
    withDensity_apply', withDensity_apply', Measure.restrict_restrict' c.finChart.open_target.measurableSet,
    Measure.restrict_restrict' ht, inter_comm, him, inter_comm (e.symm ⁻¹' T),
    lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hA hder hinj]
  refine setLIntegral_congr_fun hA fun v hv => ?_
  have hdet : ((fderiv ℂ κ v).restrictScalars ℝ).det =
      Complex.normSq (LinearMap.det (fderiv ℂ κ v : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))) :=
    ReciprocityTheory.AnForm.A.det_restrictScalars_real _
  have hleft : c.finChart.symm (κ v) = e.symm v := c.finChart.left_inv (hsub (e.map_target hv.1))
  simp only [hleft, hdet, hρ v hv.1]
  rw [abs_of_nonneg (Complex.normSq_nonneg _), ← ENNReal.ofReal_mul (Complex.normSq_nonneg _),
    Complex.normSq_eq_norm_sq]
  congr 1
  ring

end Change

section Piece

open Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M

variable {m : ℕ} {n : Fin (m + 1) → ℕ} {X : Scheme.{0}} (i : X ⟶ MP ℤ m n)

theorem mem_ptsIn_pre (W : (MP ℤ m n).Opens) (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) :
    y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ W) ↔ PtsOver.map i rfl _ y ∈ ptsIn (mpStr ℤ m n) σ₀ W := by
  rw [CxPts.mem_ptsIn, CxPts.mem_ptsIn]
  rfl

variable [IsClosedImmersion i] {D : ℕ} {e : OpenPartialHomeomorph (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (Fin D → ℂ)}
  {Γ : (Fin D → ℂ) → (Σ k, Bk n k) → ℂ}

theorem differentiableOn_coords (hΓ : DifferentiableOn ℂ Γ e.target) (hover : ∀ v ∈ e.target, Over i (e.symm v) (Γ v))
    (c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D) (hsub : e.source ⊆ c.e.source) :
    DifferentiableOn ℂ (c.finChart ∘ e.symm) e.target := by
  refine differentiableOn_pi.2 fun a => ?_
  have h := (GlobalTheory.CompanionTheory.MixZ.Holo.holo m n X i D e.target Γ e.symm e.open_target hΓ hover).2 c.U (c.x a)
  refine (h.mono fun v hv => ⟨hv, c.source_subset (hsub (e.map_target hv))⟩).congr fun v hv => ?_
  exact c.finChart_eq_ev (hsub (e.map_target hv)) a

theorem maDensity_eq (Nh : GlobalTheory.HermLB (mpStr ℤ m n)) (B : HermLine (Bk n)) (hrep : IsHermRep Nh B)
    (hΓ : DifferentiableOn ℂ Γ e.target) (hover : ∀ v ∈ e.target, Over i (e.symm v) (Γ v))
    (hmc : ∀ v ∈ e.target, ∀ k, ∃ j, Γ v ⟨k, j⟩ ≠ 0) (c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D)
    (hsub : e.source ⊆ c.e.source) {v : Fin D → ℂ} (hv : v ∈ e.target) :
    maDensity (fun _ y' => Real.log (B.h (Γ y'))) v =
      ‖LinearMap.det (fderiv ℂ (c.finChart ∘ e.symm) v : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))‖ ^ 2 *
        c.chernDens ((Nh.restr i).φ σ₀) (e.symm v) := by
  have hκd := differentiableOn_coords i hΓ hover c hsub
  set φ := (Nh.restr i).φ σ₀ with hφ
  have h : φ.IsCInf := (Nh.restr i).cInf σ₀
  set κ := c.finChart ∘ e.symm with hκ
  set y₀ := e.symm v with hy₀def
  have hy₀ : y₀ ∈ c.e.source := hsub (e.map_target hv)
  have hκv : AnalyticAt ℂ κ v := GlobalTheory.SCV.analyticAt_of_differentiableOn hκd (e.open_target.mem_nhds hv)
  have hκy : c.finChart.symm (κ v) = y₀ := c.finChart.left_inv hy₀
  have hz : κ v ∈ c.finChart.target := c.finChart.map_source hy₀
  have hma := h.maDens_eq c hz
  rw [hκy] at hma
  have hr : c.e y₀ = GlobalTheory.FinChart.toV D (κ v) := rfl
  have hd := h.contDiffAt c hy₀ (mem_pick φ.isLB y₀)
  rw [hr] at hd
  have hψ : ContDiffAt ℝ 2 (fun w => φ.locPot.φ y₀ (c.finChart.symm w)) (κ v) :=
    (hd.comp (κ v) (GlobalTheory.FinChart.toV D).contDiff.contDiffAt).div_const 2
  have hcomp := ReciprocityTheory.AnForm.A.maDens_comp (fun _ w => φ.locPot.φ y₀ (c.finChart.symm w)) κ v hκv (fun _ => hψ)
  rw [ReciprocityTheory.AnForm.A.det_jacC, Complex.normSq_eq_norm_sq, hma] at hcomp
  have hC2 : ContDiffAt ℝ 2 ((fun w => φ.locPot.φ y₀ (c.finChart.symm w)) ∘ κ) v :=
    hψ.comp v (hκv.contDiffAt.restrict_scalars ℝ)
  obtain ⟨u, hu⟩ := (isHermRep_iff Nh B).1 hrep
  choose p hp using hmc v hv
  set b := pick φ.isLB y₀ with hbdef
  have hb : PtsOver.map i rfl _ y₀ ∈ ptsIn (mpStr ℤ m n) σ₀ (Nh.B.U (b PUnit.unit)) :=
    mem_of_mem_linComb (m := fun _ => PtsOver.map i rfl _ y₀) (fun _ => rfl) (mem_pick φ.isLB y₀) PUnit.unit
  have hmch : PtsOver.map i rfl _ y₀ ∈ ptsIn (mpStr ℤ m n) σ₀ (mchart p) :=
    (GlobalTheory.CompanionTheory.MixZ.Holo.mem_ptsIn_mchart p).2 fun k => ((hover v hv) k (p k)).1.2 (hp k)
  set W := i ⁻¹ᵁ (Nh.B.U (b PUnit.unit) ⊓ mchart p) with hW
  let f : Γ(X, W) := i.app _ (u (b PUnit.unit) p).val
  set O := e.target ∩ e.symm ⁻¹' ptsIn (i ≫ mpStr ℤ m n) σ₀ W with hOdef
  have hO : IsOpen O := e.isOpen_inter_preimage_symm (isOpen_ptsIn _)
  have hvO : v ∈ O := ⟨hv, (mem_ptsIn_pre i _ _).2 (mem_ptsIn_inf.2 ⟨hb, hmch⟩)⟩
  let g : (Fin D → ℂ) → ℂ := fun w => (∏ k, Γ w ⟨k, p k⟩ ^ B.a k) * ev (i ≫ mpStr ℤ m n) σ₀ W f (e.symm w)
  have hF : AnalyticAt ℂ (ev (i ≫ mpStr ℤ m n) σ₀ W f ∘ e.symm) v :=
    GlobalTheory.SCV.analyticAt_of_differentiableOn
      ((GlobalTheory.CompanionTheory.MixZ.Holo.holo m n X i D e.target Γ e.symm e.open_target hΓ hover).2 W f) (hO.mem_nhds hvO)
  have hΓk (k) : AnalyticAt ℂ (fun w => Γ w ⟨k, p k⟩) v :=
    GlobalTheory.SCV.analyticAt_of_differentiableOn (differentiableOn_pi.1 hΓ _) (e.open_target.mem_nhds hv)
  have hg : AnalyticAt ℂ g v := (Finset.analyticAt_fun_prod _ fun k _ => (hΓk k).zpow (hp k)).mul hF
  have hunit : IsUnit f := (u (b PUnit.unit) p).isUnit.map (i.app _).hom
  have hg0 : g v ≠ 0 := mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hp k))
    (ev_ne_zero hvO.2 hunit)
  have hev : (fun w => Real.log (B.h (Γ w))) =ᶠ[𝓝 v]
      fun w => ((fun w => φ.locPot.φ y₀ (c.finChart.symm w)) ∘ κ) w + Real.log ‖g w‖ := by
    filter_upwards [hO.mem_nhds hvO] with w hw
    have hy : e.symm w ∈ c.e.source := hsub (e.map_target hw.1)
    have hmem := (mem_ptsIn_pre i _ _).1 hw.2
    have hrep' := hu.2.2 (b PUnit.unit) p (PtsOver.map i rfl _ (e.symm w)) (Γ w) (hover w hw.1) hmem
    have hzk : ∀ k, Γ w ⟨k, p k⟩ ≠ 0 := fun k =>
      ((hover w hw.1) k (p k)).1.1 (ptsIn_mono (mchart_le p k) (mem_ptsIn_inf.1 hmem).2)
    have hu0 : ev (i ≫ mpStr ℤ m n) σ₀ W f (e.symm w) ≠ 0 := ev_ne_zero hw.2 hunit
    have hev' : ev (i ≫ mpStr ℤ m n) σ₀ W f (e.symm w) =
        ev (mpStr ℤ m n) σ₀ _ (u (b PUnit.unit) p).val (PtsOver.map i rfl _ (e.symm w)) :=
      CxPts.ev_app i rfl _ _ _
    have hg0w : g w ≠ 0 := mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hzk k)) hu0
    have hnorm : ‖g w‖ = (∏ k, ‖Γ w ⟨k, p k⟩‖ ^ B.a k) *
        ‖ev (mpStr ℤ m n) σ₀ _ (u (b PUnit.unit) p).val (PtsOver.map i rfl _ (e.symm w))‖ := by
      simp only [g, norm_mul, norm_prod, norm_zpow, hev']
    have hφb : φ.φ b (e.symm w) = (Nh.φ σ₀).φ (b PUnit.unit) (PtsOver.map i rfl _ (e.symm w)) :=
      GlobalTheory.Weight.pull_φ _ i rfl b _
    have hleft : c.finChart.symm (κ w) = e.symm w := c.finChart.left_inv hy
    change Real.log (B.h (Γ w)) = φ.φ b (c.finChart.symm (κ w)) / 2 + Real.log ‖g w‖
    rw [hleft, hφb, hrep', ← hnorm, Real.log_mul (norm_ne_zero_iff.2 hg0w) (Real.exp_ne_zero _), Real.log_exp, add_comm]
  have hh : hessC (fun w => Real.log (B.h (Γ w))) v =
      hessC ((fun w => φ.locPot.φ y₀ (c.finChart.symm w)) ∘ κ) v :=
    (hessCGerm _ _ _ hev).trans (ReciprocityTheory.AnForm.A.hessC_add_log_norm _ g v hC2 hg hg0)
  change maDens (fun _ y' => Real.log (B.h (Γ y'))) v = _
  rw [maDens_congr_hessC _ (fun _ => (fun w => φ.locPot.φ y₀ (c.finChart.symm w)) ∘ κ) v fun _ => hh, hcomp]
  ring

theorem contDiffOn_log_metric {B : HermLine (Bk n)} (hB : IsSmoothHerm B) (hΓ : DifferentiableOn ℂ Γ e.target)
    (hmc : ∀ v ∈ e.target, ∀ k, ∃ j, Γ v ⟨k, j⟩ ≠ 0) :
    ContDiffOn ℝ 2 (fun y' => Real.log (B.h (Γ y'))) e.target := by
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Γ e.target :=
    (GlobalTheory.SCV.contDiffOn_of_differentiableOn e.open_target hΓ _).restrict_scalars ℝ
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y' => B.h (Γ y')) e.target := hB.comp h1 hmc
  exact (h2.log fun v hv => (B.pos _ (hmc v hv)).ne').of_le (by norm_cast)

end Piece

theorem piece_density : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (Nh : GlobalTheory.HermLB (mpStr ℤ m n)) (B : HermLine (Bk n)), IsHermRep Nh B → IsSmoothHerm B →
    ∀ (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ)
      [SecondCountableTopology (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀)]
      (Ψ : GlobalTheory.CompanionTheory.MixZ.ArchEq.LinProj n D) (N : Pol n)
      (e : OpenPartialHomeomorph (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (Fin D → ℂ)) (Γ : (Fin D → ℂ) → (Σ k, Bk n k) → ℂ),
      GlobalTheory.CompanionTheory.MixZ.ArchEq.IsPiece i Ψ N e Γ →
      ContinuousOn (maDensity (fun _ y' => Real.log (B.h (Γ y')))) e.target ∧
      ∀ ε : ℤˣ, (((Nh.restr i).φ σ₀).chernPart D ε).restrict e.source =
        ((volume.restrict e.target).withDensity fun v =>
          ENNReal.ofReal (((ε : ℤ) : ℝ) * maDensity (fun _ y' => Real.log (B.h (Γ y'))) v)).map e.symm := by
  intro m n Nh B hrep hB X _ i _ D _ Ψ N e Γ hP
  obtain ⟨⟨c, hsub⟩, hΓ, hall⟩ := hP
  have hover : ∀ v ∈ e.target, Over i (e.symm v) (Γ v) := fun v hv => (hall v hv).1
  have hmc : ∀ v ∈ e.target, ∀ k, ∃ j, Γ v ⟨k, j⟩ ≠ 0 := fun v hv => (hall v hv).2.1.1
  refine ⟨ReciprocityTheory.AnForm.M.maDens_continuousOn _ _ e.open_target fun _ => contDiffOn_log_metric i hB hΓ hmc, fun ε => ?_⟩
  exact restrict_chernPart_of_coords ((Nh.restr i).cInf σ₀) ε c e hsub (differentiableOn_coords i hΓ hover c hsub)
    fun v hv => maDensity_eq i Nh B hrep hΓ hover hmc c hsub hv

end GlobalTheory.CompanionTheory.MixZ.ArchEq.Dens
