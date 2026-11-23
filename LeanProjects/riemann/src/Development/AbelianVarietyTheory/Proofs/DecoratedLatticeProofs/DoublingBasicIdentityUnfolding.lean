import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualCFrameLat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingIntegralNegligibleOrbitsEqZeroCuspFormStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingOpenOrbitUnfoldsToAdelicIntegralStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.BasicId

open Filter Set GlobalTheory.Eis

theorem measurable_tsum_of_summable' {X I : Type} [MeasurableSpace X] [Countable I]
    (F : I → X → ℂ) (hF : ∀ i, Measurable (F i)) (hs : ∀ x, Summable fun i => F i x) :
    Measurable fun x => ∑' i, F i x :=
  measurable_of_tendsto_metrizable' (atTop : Filter (Finset I))
    (f := fun s x => ∑ i ∈ s, F i x) (fun s => Finset.measurable_sum s fun i _ => hF i)
    (tendsto_pi_nhds.2 fun x => (hs x).hasSum)

theorem out_mul_inv_mem {D : D7} (V : HSp D) (x : GQ (dblSp V)) :
    (((mk ((siegel V).subgroupOf (GQ (dblSp V))) x).out : GQ (dblSp V)) : GA D (dblSp V)) *
      ((x : GA D (dblSp V)))⁻¹ ∈ siegel V := by
  obtain ⟨γ, e⟩ := mk_eq_iff.1 (Quotient.out_eq (mk ((siegel V).subgroupOf (GQ (dblSp V))) x))
  have e' := congrArg (fun z : GQ (dblSp V) => (z : GA D (dblSp V))) e
  simp only [Subgroup.coe_mul] at e'
  rw [← e', mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]
  exact inv_mem (Subgroup.mem_subgroupOf.1 γ.2)

theorem basicIdentity_unfold : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → ∀ (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → ∀ φ ∈ degPS V a μ s, GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V (GlobalTheory.Eis.sph V a (s.re : ℂ))) → ∀ m : Measure (GA D V), m.IsHaarMeasure → ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → IsCuspFun V f₁ → GlobalTheory.Eis.BasicIdentity V μ m φ f₁ f₂ := by
  intro D V a ha μ hμ s hs φ hφ hgrow m hm f₁ f₂ h₁ h₂ hcusp
  haveI := hm
  haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  have hL : LeftInv (siegelQ V) φ := leftInv_of_mem hμ hφ
  have hφc : Continuous φ := hφ.2.1

  have hI : HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) :=
    GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D V (frameLat V) a (GlobalTheory.Core.Rk.AbsConv.isSelfDualC_frameLat V) ha
  have hS : SphConv V a := GlobalTheory.Eis.sphConv D V a hI
  have hσ : (V.rank : ℝ) / 2 < ((s.re : ℂ)).re := by simpa using hs
  have hconvS : ∀ g, EisConv V (sph V a (s.re : ℂ)) g := fun g => (((sphConv_iff hI).1 hS).1 _ hσ).2 g
  have h2 : ∀ g, sph V a (s.re : ℂ) g = (((hgt V a g : ℝ) ^ (s.re + (V.rank : ℝ) / 2) : ℝ) : ℂ) := fun g => by
    rw [Complex.ofReal_cpow (NNReal.coe_nonneg _)]; push_cast; rfl
  have hr0 : ∀ g, 0 ≤ (hgt V a g : ℝ) ^ (s.re + (V.rank : ℝ) / 2) := fun g =>
    Real.rpow_nonneg (NNReal.coe_nonneg _) _
  have hn : ∀ g, ‖sph V a (s.re : ℂ) g‖ = (hgt V a g : ℝ) ^ (s.re + (V.rank : ℝ) / 2) := fun g => by
    rw [h2, Complex.norm_real, Real.norm_of_nonneg (hr0 g)]
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C * (hgt V a g : ℝ) ^ (s.re + (V.rank : ℝ) / 2) := by
    haveI := t2Space_adeleRing' (F := D.host.F)
    exact hI.exists_norm_le continuous_absE (isCompact_Khat V a) hφ
  have hsum : ∀ y, Summable fun q : SiegelCosets V => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * y) :=
    fun y => Summable.of_norm (((hconvS y).of_norm_le (C := max C 0) fun g =>
      (hC g).trans (by rw [hn]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (hr0 g))) : EisConv V φ y)

  set P : Set (SiegelCosets V) := {q | ∃ δ ∈ GQ V, ((q.out : GQ (dblSp V)) : GA D (dblSp V)) * (io V (δ, 1))⁻¹ ∈ siegel V}
    with hP
  let e0 : GQ V → P := fun δ => ⟨mk _ ⟨io V ((δ : GA D V), 1), io_mem_GQ V δ.2 (one_mem _)⟩,
    ⟨δ, δ.2, out_mul_inv_mem V ⟨io V ((δ : GA D V), 1), io_mem_GQ V δ.2 (one_mem _)⟩⟩⟩
  have hbij : Function.Bijective e0 := by
    refine ⟨fun δ δ' h => injective_mk_io (congrArg Subtype.val h), fun q => ?_⟩
    obtain ⟨δ, hδ, hq⟩ := q.2
    refine ⟨⟨δ, hδ⟩, Subtype.ext ?_⟩
    have hm' : (q.1.out : GQ (dblSp V)) * (⟨io V (δ, 1), io_mem_GQ V hδ (one_mem _)⟩ : GQ (dblSp V))⁻¹ ∈
        (siegel V).subgroupOf (GQ (dblSp V)) := Subgroup.mem_subgroupOf.2 (by simpa using hq)
    exact (mk_eq_iff.2 ⟨⟨_, hm'⟩, by simp⟩).trans q.1.out_eq
  have hterm : ∀ (δ : GQ V) y, φ ((((e0 δ).1.out : GQ (dblSp V)) : GA D (dblSp V)) * y) = φ (io V ((δ : GA D V), 1) * y) :=
    fun δ y => term_mk hL y ⟨io V ((δ : GA D V), 1), io_mem_GQ V δ.2 (one_mem _)⟩
  obtain ⟨Eo, hEo⟩ : ∃ Eo : GA D (dblSp V) → ℂ, Eo = fun y => ∑' δ : GQ V, φ (io V (δ, 1) * y) := ⟨_, rfl⟩
  obtain ⟨En, hEn⟩ : ∃ En : GA D (dblSp V) → ℂ, En = fun y => ∑' q : {q : GlobalTheory.Eis.SiegelCosets V // ¬ ∃ δ ∈ GQ V,
      ((q.out : GQ (dblSp V)) : GA D (dblSp V)) * (io V (δ, 1))⁻¹ ∈ siegel V},
      φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * y) := ⟨_, rfl⟩
  have hEoP : ∀ y, Eo y = ∑' q : P, φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * y) := fun y => by
    rw [hEo, ← (Equiv.ofBijective e0 hbij).tsum_eq]
    exact tsum_congr fun δ => (hterm δ y).symm
  have hsumO : ∀ y, Summable fun δ : GQ V => φ (io V ((δ : GA D V), 1) * y) := fun y => by
    have := ((Equiv.ofBijective e0 hbij).summable_iff (f := fun q : P =>
      φ (((q.1.out : GQ (dblSp V)) : GA D (dblSp V)) * y))).2 ((hsum y).subtype P)
    exact this.congr fun δ => hterm δ y
  have hsplit : ∀ y, eis V φ y = Eo y + En y := fun y => by
    rw [hEoP, hEn]
    exact ((hsum y).tsum_subtype_add_tsum_subtype_compl P).symm

  have hEoInv : ∀ γ ∈ (GQ V).prod (GQ V), ∀ y, Eo (io V γ * y) = Eo y := by
    rintro ⟨γ₁, γ₂⟩ ⟨h1, h2⟩ y
    let e : GQ V ≃ GQ V := (Equiv.mulLeft (⟨γ₂, h2⟩ : GQ V)⁻¹).trans (Equiv.mulRight ⟨γ₁, h1⟩)
    rw [hEo]
    show ∑' δ : GQ V, φ (io V ((δ : GA D V), 1) * (io V (γ₁, γ₂) * y)) = ∑' δ : GQ V, φ (io V ((δ : GA D V), 1) * y)
    rw [← e.tsum_eq (fun δ : GQ V => φ (io V ((δ : GA D V), 1) * y))]
    refine tsum_congr fun δ => ?_
    have hd : io V ((δ : GA D V), 1) * (io V (γ₁, γ₂) * y) = io V (γ₂, γ₂) * (io V (((e δ : GQ V) : GA D V), 1) * y) := by
      rw [← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul]
      congr 2
      refine Prod.ext ?_ ?_
      · simp [e, mul_assoc]
      · simp
    rw [hd, hL _ ⟨(io_mem_siegel V).2 rfl, io_mem_GQ V h2 h2⟩]
  have hi : LeftInv ((GQ V).prod (GQ V)) (dblIntegrand V μ Eo f₁ f₂) := fun γ hγ g => by
    simp only [dblIntegrand, map_mul (io V), hEoInv γ hγ, Prod.fst_mul, Prod.snd_mul, h₁.1 _ hγ.1, h₂.1 _ hγ.2,
      map_mul (detA V), map_mul μ, apply_detA hμ hγ.2, one_mul]

  have hEom : Measurable Eo := by
    rw [hEo]
    exact measurable_tsum_of_summable' (fun δ : GQ V => fun y => φ (io V ((δ : GA D V), 1) * y))
      (fun δ => (hφc.comp (continuous_const.mul continuous_id)).measurable) hsumO
  have hDm : Measurable (dblIntegrand V μ Eo f₁ f₂) := by
    have e : dblIntegrand V μ Eo f₁ f₂ = fun g => Eo (io V g) * dblIntegrand V μ (fun _ => 1) f₁ f₂ g :=
      funext fun g => by simp only [dblIntegrand]; ring
    rw [e]
    exact (hEom.comp (continuous_io V).measurable).mul
      (continuous_dblIntegrand hμ continuous_const h₁.continuous h₂.continuous).measurable

  have h𝓕 := isFundamentalDomain_stdDom (GQ V) m
  have habs := GlobalTheory.Core.Rk.AbsConv.absConv_unfolded D V a ha μ hμ s hs φ hφ hgrow m hm f₁ f₂ h₁ h₂
  have hfin := habs.1 _ h𝓕
  have hmeasq : ∀ q : SiegelCosets V, AEMeasurable (fun x =>
      ‖dblIntegrand V μ (fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂ x‖ₑ)
      ((m.prod m).restrict (stdDom (GQ V) ×ˢ stdDom (GQ V))) := fun q =>
    (continuous_dblIntegrand hμ (hφc.comp (continuous_const.mul continuous_id)) h₁.continuous
      h₂.continuous).measurable.enorm.aemeasurable
  have hpt : ∀ x, ‖dblIntegrand V μ Eo f₁ f₂ x‖ₑ ≤ ∑' q : SiegelCosets V,
      ‖dblIntegrand V μ (fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂ x‖ₑ := fun x => by
    simp only [GlobalTheory.Core.Rk.AbsConv.enorm_dblIntegrand]
    rw [ENNReal.tsum_mul_right]
    gcongr ?_ * _
    rw [hEoP]
    exact enorm_tsum_le_tsum_enorm.trans (ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _)
  have hOn : IntegrableOn (dblIntegrand V μ Eo f₁ f₂) (stdDom (GQ V) ×ˢ stdDom (GQ V)) (m.prod m) := by
    refine ⟨hDm.aestronglyMeasurable, ?_⟩
    show ∫⁻ x in stdDom (GQ V) ×ˢ stdDom (GQ V), ‖dblIntegrand V μ Eo f₁ f₂ x‖ₑ ∂m.prod m < ⊤
    calc _ ≤ ∫⁻ x in stdDom (GQ V) ×ˢ stdDom (GQ V), ∑' q : SiegelCosets V,
          ‖dblIntegrand V μ (fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂ x‖ₑ ∂m.prod m :=
          lintegral_mono hpt
      _ = _ := lintegral_tsum hmeasq
      _ < ⊤ := hfin.lt_top
  have hEoC : DblConv V μ m Eo f₁ f₂ := (dblConv_iff hi hDm h𝓕).2 hOn

  have hQ : ∀ q, dblIntegrandQ V μ (eis V φ) f₁ f₂ q = dblIntegrandQ V μ Eo f₁ f₂ q + dblIntegrandQ V μ En f₁ f₂ q :=
    fun q => by simp only [dblIntegrandQ, dblIntegrand, hsplit]; ring
  have hEnI : Integrable (dblIntegrandQ V μ En f₁ f₂) ((autMeasure V m).prod (autMeasure V m)) :=
    (habs.2.2.sub hEoC.2).congr (Eventually.of_forall fun q => by simp only [Pi.sub_apply, hQ]; ring)
  have h6 := GlobalTheory.T.doubling_integral_negligible_orbits_eq_zero_cuspForm D V a ha μ hμ s hs φ hφ hgrow m hm f₁ f₂ h₁ h₂ hcusp
  have h7 := GlobalTheory.T.doubling_open_orbit_unfolds_to_adelic_integral D V a ha μ hμ s hs φ hφ hgrow m hm f₁ f₂ h₁ h₂
  rw [← hEn] at h6
  rw [← hEo] at h7
  refine ⟨habs.2, h7.1, ?_⟩
  show ∫ q, dblIntegrandQ V μ (eis V φ) f₁ f₂ q ∂(autMeasure V m).prod (autMeasure V m) = _
  rw [integral_congr_ae (Eventually.of_forall hQ), integral_add hEoC.2 hEnI, h7.2, h6, add_zero]

end GlobalTheory.Core.Rk.BasicId

end
