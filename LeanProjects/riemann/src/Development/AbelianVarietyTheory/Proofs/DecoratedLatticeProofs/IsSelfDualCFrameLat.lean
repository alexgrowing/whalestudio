import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableUnitaryQuotientHeightPowMulRapidlyDecrStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetGramSmul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHeightDoublingEmbeddingLePowMulHeights
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.AbsConv

open Filter Set GlobalTheory.Eis

theorem isSelfDualC_frameLat {D : D7} (V : HSp D) : IsSelfDualC V (frameLat V) := by
  have h : frameLat V = GlobalTheory.PlaceModel.latFrame V :=
    Submodule.ext fun y => (mem_frameLat V y).trans (GlobalTheory.PlaceModel.mem_latFrame V y).symm
  rw [h]
  exact GlobalTheory.PlaceModel.isSelfDualC_latFrame V

theorem enorm_dblIntegrand {D : D7} {V : HSp D} (μ : (AE D)ˣ →* Circle) (E : GA D (dblSp V) → ℂ)
    (f₁ f₂ : GA D V → ℂ) (x : GA D V × GA D V) :
    ‖dblIntegrand V μ E f₁ f₂ x‖ₑ = ‖E (io V x)‖ₑ * (‖f₁ x.1‖ₑ * ‖f₂ x.2‖ₑ) := by
  simp only [dblIntegrand]
  simp_rw [← ofReal_norm_eq_enorm]
  rw [norm_mul, norm_mul, norm_mul, norm_inv, Circle.norm_coe, inv_one, mul_one, Complex.norm_conj,
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), mul_assoc]

theorem dblConv_of_growth {D : D7} {V : HSp D} {μ : (AE D)ˣ →* Circle} (hμ : IsHeckeChar D μ)
    {m : Measure (GA D V)} (hm : m.IsHaarMeasure) {f₁ f₂ : GA D V → ℂ} (h₁ : GlobalTheory.Grow.RapidDec V f₁)
    (h₂ : GlobalTheory.Grow.RapidDec V f₂) {E : GA D (dblSp V) → ℂ} (hE : LeftInv (GQ (dblSp V)) E) (hc : Continuous E)
    {C : ℝ} {N : ℕ} (hb : ∀ g, ‖E g‖ ≤ C * GlobalTheory.Grow.height (dblSp V) g ^ N) :
    DblConv V μ m E f₁ f₂ := by
  have hli : LeftInv ((GQ V).prod (GQ V)) (dblIntegrand V μ E f₁ f₂) := leftInv_dblIntegrand hμ hE h₁.1 h₂.1
  have hmeas : AEStronglyMeasurable (dblIntegrandQ V μ E f₁ f₂) ((autMeasure V m).prod (autMeasure V m)) := by
    have e' : dblIntegrandQ V μ E f₁ f₂ = dblIntegrand V μ E f₁ f₂ ∘ Prod.map (sec (GQ V)) (sec (GQ V)) :=
      funext fun q => (congrArg _ (Prod.ext (mk_sec q.1) (mk_sec q.2)).symm).trans (dblIntegrandQ_mk hli _ _)
    rw [e']
    exact ((continuous_dblIntegrand hμ hc h₁.continuous h₂.continuous).measurable.comp
      (measurableEmbedding_sec.measurable.prodMap measurableEmbedding_sec.measurable)).aestronglyMeasurable
  have i₁ := GlobalTheory.T.integrable_unitaryQuotientHeight_pow_mul_rapidlyDecreasing D V m hm f₁ h₁ N
  have i₂ := GlobalTheory.T.integrable_unitaryQuotientHeight_pow_mul_rapidlyDecreasing D V m hm f₂ h₂ N
  set K : ℝ := max C 0 * 4 ^ N with hK
  have hK0 : 0 ≤ K := mul_nonneg (le_max_right _ _) (by positivity)
  refine ⟨hli, ((i₁.mul_prod i₂).const_mul K).mono' hmeas (Eventually.of_forall fun q => ?_)⟩
  obtain ⟨γ₁, hγ₁, e₁⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight V q.1.out
  obtain ⟨γ₂, hγ₂, e₂⟩ := GlobalTheory.Grow.exists_height_le_two_mul_quotHeight V q.2.out
  have hinv : E (io V (q.1.out, q.2.out)) = E (io V (γ₁ * q.1.out, γ₂ * q.2.out)) := by
    have e : io V (γ₁ * q.1.out, γ₂ * q.2.out) = io V (γ₁, γ₂) * io V (q.1.out, q.2.out) := by
      rw [← map_mul]; rfl
    rw [e, hE _ (io_mem_GQ V hγ₁ hγ₂)]
  have hq₁ := GlobalTheory.Grow.one_le_quotHeight V q.1.out
  have hq₂ := GlobalTheory.Grow.one_le_quotHeight V q.2.out
  have hx₁ := GlobalTheory.Grow.one_le_height V (γ₁ * q.1.out)
  have hx₂ := GlobalTheory.Grow.one_le_height V (γ₂ * q.2.out)
  have h3 : GlobalTheory.Grow.height (dblSp V) (io V (γ₁ * q.1.out, γ₂ * q.2.out)) ≤
      4 * (GlobalTheory.Grow.quotHeight V q.1.out * GlobalTheory.Grow.quotHeight V q.2.out) := by
    refine (GlobalTheory.Cont.HeightIo.height_io_le_mul V _ _).trans ?_
    nlinarith
  have h0 : 1 ≤ GlobalTheory.Grow.height (dblSp V) (io V (γ₁ * q.1.out, γ₂ * q.2.out)) := GlobalTheory.Grow.one_le_height _ _
  have hEq : ‖E (io V (q.1.out, q.2.out))‖ ≤
      K * (GlobalTheory.Grow.quotHeight V q.1.out ^ N * GlobalTheory.Grow.quotHeight V q.2.out ^ N) := by
    rw [hinv]
    calc _ ≤ C * GlobalTheory.Grow.height (dblSp V) (io V (γ₁ * q.1.out, γ₂ * q.2.out)) ^ N := hb _
      _ ≤ max C 0 * (4 * (GlobalTheory.Grow.quotHeight V q.1.out * GlobalTheory.Grow.quotHeight V q.2.out)) ^ N :=
          mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ (by linarith) h3 N) (pow_nonneg (by linarith) N)
            (le_max_right _ _)
      _ = _ := by rw [hK, mul_pow, mul_pow]; ring
  have hμ1 : ‖((μ (detA V q.2.out) : ℂ))⁻¹‖ = 1 := by
    rw [norm_inv, Circle.norm_coe, inv_one]
  simp only [dblIntegrandQ, dblIntegrand, norm_mul, hμ1, mul_one, Complex.norm_conj]
  calc ‖E (io V (q.1.out, q.2.out))‖ * ‖f₁ q.1.out‖ * ‖f₂ q.2.out‖
      ≤ K * (GlobalTheory.Grow.quotHeight V q.1.out ^ N * GlobalTheory.Grow.quotHeight V q.2.out ^ N) *
          ‖f₁ q.1.out‖ * ‖f₂ q.2.out‖ := by gcongr
    _ = _ := by ring

theorem absConv_unfolded : ∀ (D : D7) (V : HSp D) (a : GL (Fin V.rank) (AE D)), IsMaj V a → ∀ (μ : (AE D)ˣ →* Circle),
    IsHeckeChar D μ → ∀ s : ℂ, (V.rank : ℝ) / 2 < s.re → ∀ φ ∈ degPS V a μ s,
    GlobalTheory.Grow.ModGrowth (dblSp V) (GlobalTheory.Eis.eis V (GlobalTheory.Eis.sph V a (s.re : ℂ))) → ∀ m : Measure (GA D V),
    m.IsHaarMeasure → ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ →
    (∀ 𝓕 : Set (GA D V), IsFundamentalDomain (GQ V) 𝓕 m → ∑' q : GlobalTheory.Eis.SiegelCosets V, ∫⁻ x in 𝓕 ×ˢ 𝓕,
      ‖GlobalTheory.Eis.dblIntegrand V μ (fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂ x‖ₑ ∂m.prod m ≠ ⊤) ∧
    GlobalTheory.Eis.DblConv V μ m (GlobalTheory.Eis.eis V φ) f₁ f₂ := by
  intro D V a ha μ hμ s hs φ hφ hgrow m hm f₁ f₂ h₁ h₂
  have hI : HasIwasawa D.sp.cm.sig (dblSp V).gram (Khat V a) :=
    GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D V (frameLat V) a (isSelfDualC_frameLat V) ha
  have hS : SphConv V a := GlobalTheory.Eis.sphConv D V a hI
  have hσ : (V.rank : ℝ) / 2 < ((s.re : ℂ)).re := by simpa using hs
  have hconvS : ∀ g, EisConv V (sph V a (s.re : ℂ)) g := fun g => (((sphConv_iff hI).1 hS).1 _ hσ).2 g
  have h2 : ∀ g, sph V a (s.re : ℂ) g = (((hgt V a g : ℝ) ^ (s.re + (V.rank : ℝ) / 2) : ℝ) : ℂ) := fun g => by
    rw [Complex.ofReal_cpow (NNReal.coe_nonneg _)]; push_cast; rfl
  have hr0 : ∀ g, 0 ≤ (hgt V a g : ℝ) ^ (s.re + (V.rank : ℝ) / 2) := fun g =>
    Real.rpow_nonneg (NNReal.coe_nonneg _) _
  have hn : ∀ g, ‖sph V a (s.re : ℂ) g‖ = (hgt V a g : ℝ) ^ (s.re + (V.rank : ℝ) / 2) := fun g => by
    rw [h2, Complex.norm_real, Real.norm_of_nonneg (hr0 g)]
  have hsS : ∀ g, Summable fun q : SiegelCosets V =>
      ‖sph V a (s.re : ℂ) (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * g)‖ := fun g => hconvS g
  have heS : ∀ g, ‖eis V (sph V a (s.re : ℂ)) g‖ =
      ∑' q : SiegelCosets V, ‖sph V a (s.re : ℂ) (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * g)‖ := by
    intro g
    have e : eis V (sph V a (s.re : ℂ)) g = ((∑' q : SiegelCosets V,
        ‖sph V a (s.re : ℂ) (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * g)‖ : ℝ) : ℂ) := by
      rw [Complex.ofReal_tsum]
      exact tsum_congr fun q => by rw [hn]; exact h2 _
    rw [e, Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg fun _ => norm_nonneg _)]
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ g, ‖φ g‖ ≤ C * (hgt V a g : ℝ) ^ (s.re + (V.rank : ℝ) / 2) := by
    haveI := t2Space_adeleRing' (F := D.host.F)
    exact hI.exists_norm_le continuous_absE (isCompact_Khat V a) hφ
  have hφS : ∀ g, ‖φ g‖ ≤ max C 0 * ‖sph V a (s.re : ℂ) g‖ := fun g =>
    (hC g).trans (by rw [hn]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (hr0 g))
  have hsφ : ∀ y, Summable fun q : SiegelCosets V => ‖φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * y)‖ :=
    fun y => Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => hφS _) ((hsS y).mul_left _)
  have hle : ∀ y, ∑' q : SiegelCosets V, ‖φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * y)‖ ≤
      max C 0 * ‖eis V (sph V a (s.re : ℂ)) y‖ := fun y => by
    rw [heS, ← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun q => hφS _) (hsφ y) ((hsS y).mul_left _)
  obtain ⟨B, A, hB⟩ := hgrow
  have h1 : IsHeckeChar D 1 := ⟨continuous_const, fun _ => rfl⟩
  have hSi : LeftInv (GQ (dblSp V)) (eis V (sph V a (s.re : ℂ))) := leftInv_eis (leftInv_of_mem h1 (sph_mem hI _))
  have hSc : Continuous (eis V (sph V a (s.re : ℂ))) := SphConv.continuous_eis hI (sph_mem hI _) hS hσ
  have hconv0 : DblConv V μ m (fun y => (((max C 0 * ‖eis V (sph V a (s.re : ℂ)) y‖ : ℝ)) : ℂ)) f₁ f₂ := by
    refine dblConv_of_growth hμ hm h₁ h₂ (C := max C 0 * B) (N := A) (fun γ hγ g => ?_)
      (Complex.continuous_ofReal.comp (continuous_const.mul hSc.norm)) (fun g => ?_)
    · beta_reduce
      rw [hSi γ hγ g]
    · rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (le_max_right _ _) (norm_nonneg _)), mul_assoc]
      exact mul_le_mul_of_nonneg_left (hB g) (le_max_right _ _)
  refine ⟨fun 𝓕 h𝓕 => ?_, ?_⟩
  · have hint := (hconv0.dblInt_eq h𝓕).1
    have hφc : Continuous φ := hφ.2.1
    have hmeas : ∀ q : SiegelCosets V, AEMeasurable (fun x =>
        ‖dblIntegrand V μ (fun x => φ (((q.out : GQ (dblSp V)) : GA D (dblSp V)) * x)) f₁ f₂ x‖ₑ)
        ((m.prod m).restrict (𝓕 ×ˢ 𝓕)) := fun q =>
      (continuous_dblIntegrand hμ (hφc.comp (continuous_const.mul continuous_id)) h₁.continuous
        h₂.continuous).measurable.enorm.aemeasurable
    rw [← lintegral_tsum hmeas]
    refine ne_top_of_le_ne_top hint.2.ne (lintegral_mono fun x => ?_)
    simp only [enorm_dblIntegrand]
    rw [ENNReal.tsum_mul_right]
    gcongr ?_ * _
    simp_rw [← ofReal_norm_eq_enorm]
    rw [Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (le_max_right _ _) (norm_nonneg _)),
      ← ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hsφ _)]
    exact ENNReal.ofReal_le_ofReal (hle _)
  · refine dblConv_of_growth hμ hm h₁ h₂ (leftInv_eis (leftInv_of_mem hμ hφ)) (SphConv.continuous_eis hI hφ hS hs)
      (C := max C 0 * B) (N := A) fun g => ?_
    refine (norm_tsum_le_tsum_norm (hsφ g)).trans ((hle g).trans ?_)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hB g) (le_max_right _ _)

end GlobalTheory.Core.Rk.AbsConv

end
