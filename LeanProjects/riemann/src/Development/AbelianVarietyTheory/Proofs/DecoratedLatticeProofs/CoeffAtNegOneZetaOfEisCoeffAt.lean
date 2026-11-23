import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingZetaValueAtEisensteinHolomorphicPoint
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

open Filter Topology Set Metric GlobalTheory.Eis

namespace GlobalTheory.Eis.Residue

theorem isExtAt_sub (a s₀ : ℂ) : IsExtAt (fun s : ℂ => s - a) s₀ fun s => s - a :=
  (isMerExt_self isRightDomain_univ fun s _ => (MeromorphicAt.id s).sub (MeromorphicAt.const a s)).isExtAt trivial

theorem coeffAt_neg_one_of_holValueAt {h : ℂ → ℂ} {a c : ℂ} (hv : HolValueAt (fun s => (s - a) * h s) a c) :
    CoeffAt h a (-1) c := by
  obtain ⟨H, hx, han, hH⟩ := hv
  have hx' : IsExtAt h a fun s => H s / (s - a) := by
    refine (hx.div (isExtAt_sub a a)).congr ⟨a.re, fun s hs => ?_⟩
    have : s - a ≠ 0 := sub_ne_zero.2 (by rintro rfl; exact lt_irrefl _ (mem_rightOf.1 hs))
    simp only
    field_simp
  have t : Tendsto (fun s => (s - a) ^ (1 : ℕ) * (H s / (s - a))) (𝓝[≠] a) (𝓝 c) := by
    refine (hH ▸ han.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have : s - a ≠ 0 := sub_ne_zero.2 hs
    field_simp
  simpa using hx'.coeffAt_of_tendsto t

theorem cont_sub_mul {h : ℂ → ℂ} (hc : Continues h) (a s : ℂ) (hs : ContinuousAt (cont h) s) :
    cont (fun t => (t - a) * h t) s = (s - a) * cont h s := by
  obtain ⟨E, hE⟩ := hc
  have hx := hE.isExtAt (s₀ := s) trivial
  have hv : HolValueAt h s (cont h s) :=
    hx.holValueAt_iff.2 ((hs.tendsto.mono_left nhdsWithin_le_nhds).congr' hx.cont_eventuallyEq)
  have hl : HolValueAt (fun t : ℂ => t - a) s (s - a) := ⟨_, isExtAt_sub a s, by fun_prop, rfl⟩
  exact (hl.mul hv).valueAt.cont_eq

variable {D : D7} {V : HSp D} {Φ : ℂ → GA D (dblSp V) → ℂ}

theorem eisSer_sub_smul (s₀ : ℂ) (g : GA D (dblSp V)) :
    eisSer V ((fun s => s - s₀) • Φ) g = fun s => (s - s₀) * eisSer V Φ g s := by
  funext s
  show eis V ((s - s₀) • Φ s) g = _
  rw [eis_smul]; rfl

theorem isZetaFamily_sub_smul {μ : (AE D)ˣ →* Circle} {m : Measure (GA D V)} {f₁ f₂ : GA D V → ℂ}
    (hZ : IsZetaFamily V μ m Φ f₁ f₂) (s₀ : ℂ) : IsZetaFamily V μ m ((fun s => s - s₀) • Φ) f₁ f₂ := by
  refine ⟨hZ.1.smul _, fun s hs => ?_⟩
  obtain ⟨hl, hi⟩ := hZ.2 s hs
  have e1 : eis V (((fun s => s - s₀) • Φ) s) = (s - s₀) • eis V (Φ s) := eis_smul _ _
  have e2 : dblIntegrand V μ ((s - s₀) • eis V (Φ s)) f₁ f₂ = fun q => (s - s₀) * dblIntegrand V μ (eis V (Φ s)) f₁ f₂ q :=
    funext fun q => by simp only [dblIntegrand, Pi.smul_apply, smul_eq_mul]; ring
  have e3 : dblIntegrandQ V μ ((s - s₀) • eis V (Φ s)) f₁ f₂ =
      fun q => (s - s₀) * dblIntegrandQ V μ (eis V (Φ s)) f₁ f₂ q :=
    funext fun q => by simp only [dblIntegrandQ, e2]
  rw [e1]
  refine ⟨fun γ hγ g => ?_, ?_⟩
  · rw [e2]; exact congrArg _ (hl γ hγ g)
  · rw [e3]; exact hi.const_mul _

theorem eisContinues_sub_smul (hE : EisContinues V Φ) (s₀ : ℂ) : EisContinues V ((fun s => s - s₀) • Φ) := by
  refine ⟨hE.1.smul _, fun g => ?_⟩
  obtain ⟨E, hE'⟩ := hE.2 g
  rw [eisSer_sub_smul]
  exact ⟨fun s => (s - s₀) * E s, isRightDomain_univ,
    fun s _ => ((MeromorphicAt.id s).sub (MeromorphicAt.const s₀ s)).mul (hE'.2.1 s trivial),
    (EqRight.refl (fun s : ℂ => s - s₀)).map₂ (· * ·) hE'.2.2⟩

theorem eisRegularAt_sub_smul (hE : EisContinues V Φ) (s₀ s₁ : ℂ) {k : ℕ} (h : EisRegularAt V Φ s₁ k) :
    EisRegularAt V ((fun s => s - s₀) • Φ) s₁ k := by
  obtain ⟨r, H, hr, e, hd, hc, C, N, hb⟩ := h
  have hcont : ∀ s ∈ ball s₁ r, s ≠ s₁ → ∀ g,
      eisCont V ((fun s => s - s₀) • Φ) s g = (s - s₀) * eisCont V Φ s g := by
    intro s hs h0 g
    simp only [eisCont, eisSer_sub_smul]
    refine cont_sub_mul (hE.2 g) s₀ s ?_
    have hU : ball s₁ r \ {s₁} ∈ 𝓝 s := (isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hs, h0⟩
    have ht : ContinuousAt (fun t => H t g / (t - s₁) ^ k) s :=
      ((hd g).continuousOn.continuousAt (isOpen_ball.mem_nhds hs)).div (by fun_prop)
        (pow_ne_zero _ (sub_ne_zero.2 h0))
    refine ht.congr ?_
    filter_upwards [hU] with t ht'
    rw [e t ht'.1 ht'.2 g]
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ (sub_ne_zero.2 ht'.2))
  refine ⟨r, fun s g => (s - s₀) * H s g, hr, fun s hs h0 g => ?_, fun g => (differentiableOn_id.sub_const _).mul (hd g),
    (by fun_prop : ContinuousOn (fun x : ℂ × GA D (dblSp V) => x.1 - s₀) _).mul hc, (‖s₁ - s₀‖ + r) * C, N,
    fun s hs g => ?_⟩
  · show (s - s₀) * H s g = _
    rw [hcont s hs h0 g, e s hs h0 g]; ring
  · rw [norm_mul, mul_assoc]
    have h1 : ‖s - s₀‖ ≤ ‖s₁ - s₀‖ + r := by
      calc ‖s - s₀‖ = ‖(s - s₁) + (s₁ - s₀)‖ := by ring_nf
        _ ≤ ‖s - s₁‖ + ‖s₁ - s₀‖ := norm_add_le _ _
        _ ≤ ‖s₁ - s₀‖ + r := by linarith [(mem_ball_iff_norm.1 hs).le]
    exact mul_le_mul h1 (hb s hs g) (norm_nonneg _) (add_nonneg (norm_nonneg _) hr.le)

theorem eisValueAt_sub_smul {s₀ : ℂ} {E₁ : GA D (dblSp V) → ℂ} (hp : EisPoleLE V Φ s₀ 1)
    (hc : EisCoeffAt V Φ s₀ (-1) E₁) : EisValueAt V ((fun s => s - s₀) • Φ) s₀ E₁ := by
  refine ⟨hp.1.smul _, fun g => ?_⟩
  obtain ⟨E, hx, -⟩ := id (hp.2 g)
  have t := hx.tendsto_of_poleLE (hp.2 g) (c := E₁ g) (by simpa using hc.2 g)
  rw [eisSer_sub_smul]
  exact ((isExtAt_sub s₀ s₀).mul hx).holValueAt_iff.2 (by simpa using t)

end GlobalTheory.Eis.Residue

namespace GlobalTheory.Eis

open GlobalTheory.Eis.Residue

theorem coeffAt_neg_one_zeta_of_eisCoeffAt : ∀ (D : D7) (V : HSp D) (μ : (AE D)ˣ →* Circle), IsHeckeChar D μ → ∀ (m : Measure (GA D V)), m.IsHaarMeasure → ∀ (Φ : ℂ → GA D (dblSp V) → ℂ), GlobalTheory.Eis.EisContinues V Φ → (∀ g, AnalyticOnNhd ℂ (GlobalTheory.Eis.eisSer V Φ g) (rightOf (V.rank / 2))) → (∀ s₀, ∃ k, GlobalTheory.Eis.EisRegularAt V Φ s₀ k) → ∀ f₁ f₂ : GA D V → ℂ, GlobalTheory.Grow.RapidDec V f₁ → GlobalTheory.Grow.RapidDec V f₂ → GlobalTheory.Eis.IsZetaFamily V μ m Φ f₁ f₂ → ∀ (s₀ : ℂ) (E₁ : GA D (dblSp V) → ℂ), GlobalTheory.Eis.EisPoleLE V Φ s₀ 1 → GlobalTheory.Eis.EisCoeffAt V Φ s₀ (-1) E₁ → CoeffAt (GlobalTheory.Eis.zeta V μ m Φ f₁ f₂) s₀ (-1) (GlobalTheory.Eis.dblInt V μ m E₁ f₁ f₂) := by
  intro D V μ hμ m hm Φ hE ha hreg f₁ f₂ h₁ h₂ hZ s₀ E₁ hp hc
  have han : ∀ g, AnalyticOnNhd ℂ (eisSer V ((fun s => s - s₀) • Φ) g) (rightOf (V.rank / 2)) := fun g => by
    rw [eisSer_sub_smul]
    exact fun s hs => (analyticAt_id.sub analyticAt_const).mul (ha g s hs)
  have hv := (zetaHolValueAt_of_eisValueAt D V μ hμ m hm ((fun s => s - s₀) • Φ) (eisContinues_sub_smul hE s₀) han
    (fun s₁ => let ⟨k, h⟩ := hreg s₁; ⟨k, eisRegularAt_sub_smul hE s₀ s₁ h⟩) f₁ f₂ h₁ h₂
    (isZetaFamily_sub_smul hZ s₀) s₀ E₁ (eisValueAt_sub_smul hp hc)).2.2
  have ez : zeta V μ m ((fun s => s - s₀) • Φ) f₁ f₂ = fun s => (s - s₀) * zeta V μ m Φ f₁ f₂ s := funext fun s => by
    have e2 := dblInt_smul (V := V) (μ := μ) (m := m) (E := eis V (Φ s)) (f₁ := f₁) (f₂ := f₂) (s - s₀) 1 1
    simp only [one_smul, map_one, mul_one] at e2
    show dblInt V μ m (eis V ((s - s₀) • Φ s)) f₁ f₂ = _
    rw [eis_smul, e2]; rfl
  rw [ez] at hv
  exact coeffAt_neg_one_of_holValueAt hv

end GlobalTheory.Eis
