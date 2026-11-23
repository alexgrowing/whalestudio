import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BcMapBcVec
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.FlatChernWeightEqOfIndependence
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.OnbMat
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.RegularFormsIsBundleProjectiveCover
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TwistedDualRegularFormsFiniteCover
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CuspOnto
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.AdelicGLLastRowAndDetModuleUnderLeftMultiplicati
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Statements.GeometryStatements.LamLevel
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ThmFlatA
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.MetricStatements.SmallOnTower
import Development.AutomorphicSpectrum.Statements.MetricStatements.RankBound
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.ShareLow
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.LineDegreeClosedFormula
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompactificationCompEquiv
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CuspSquareIntegrableIffUnfolded
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
import Development.AbelianVarietyTheory.Proofs.HeightProofs.VolPairExAndFinVol
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagQuotientIntegralEqUniversalConstMulStatement
import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.ExistsFundSetOrth
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace PositivityTheory.Xgy

namespace PetTie

open scoped ENNReal

theorem integral_transfer {A B : Type} [MeasurableSpace A] [MeasurableSpace B] (μ : Measure A) (ν : Measure B)
    (C : ℝ≥0∞) {φ : A → ℂ} {ψ : B → ℂ} (hφ : Measurable φ) (hψ : Measurable ψ)
    (h : ∀ G : ℂ → ℝ≥0∞, Measurable G → G 0 = 0 → ∫⁻ a, G (φ a) ∂μ = C * ∫⁻ b, G (ψ b) ∂ν) :
    ∫ a, φ a ∂μ = (C.toReal : ℂ) * ∫ b, ψ b ∂ν := by
  have hs : MeasurableSet ({0}ᶜ : Set ℂ) := (measurableSet_singleton 0).compl
  have e : (μ.map φ).restrict {0}ᶜ = C • (ν.map ψ).restrict {0}ᶜ := by
    ext s hs'
    have hm := hs'.inter hs
    have := h ((s ∩ {0}ᶜ).indicator 1) (measurable_one.indicator hm) (by simp)
    rw [← lintegral_map (measurable_one.indicator hm) hφ, ← lintegral_map (measurable_one.indicator hm) hψ,
      lintegral_indicator_one hm, lintegral_indicator_one hm] at this
    rw [Measure.smul_apply, Measure.restrict_apply hs', Measure.restrict_apply hs', this, smul_eq_mul]
  have k1 : ∀ ρ : Measure ℂ, ∫ z in ({0}ᶜ : Set ℂ), z ∂ρ = ∫ z, z ∂ρ := fun ρ =>
    setIntegral_eq_integral_of_forall_compl_eq_zero (by simp)
  have k2 : ∫ a, φ a ∂μ = ∫ z, z ∂(μ.map φ) := (integral_map hφ.aemeasurable aestronglyMeasurable_id).symm
  have k3 : ∫ a, ψ a ∂ν = ∫ z, z ∂(ν.map ψ) := (integral_map hψ.aemeasurable aestronglyMeasurable_id).symm
  rw [k2, k3, ← k1, ← k1 (ν.map ψ), e, integral_smul_measure, Complex.real_smul]

section FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def prd (X : Data E r) (la : Wt X.Ψ r) (P Q : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : ℂ :=
  P x * starRingEnd ℂ (Q x) * ((X.nfac la x ^ 2 : ℝ) : ℂ)

theorem prd_eq_of (X : Data E r) (la : Wt X.Ψ r) {P Q : Frame X.Ψ r → ℂ} {x y : Frame X.Ψ r} {t : ℂ}
    (hP : P y = t * P x) (hQ : Q y = t * Q x) (hn : X.pnorm la P y = X.pnorm la P x) :
    prd X la P Q y = prd X la P Q x := by
  unfold prd
  by_cases h0 : P x = 0
  · simp [hP, h0]
  · have h1 : ‖P y‖ * X.nfac la y = ‖P x‖ * X.nfac la x := hn
    rw [hP, norm_mul, mul_right_comm, mul_comm ‖P x‖] at h1
    have h2 : ‖t‖ * X.nfac la y = X.nfac la x := mul_right_cancel₀ (norm_ne_zero_iff.2 h0) h1
    rw [hP, hQ, ← h2, map_mul, mul_pow, Complex.ofReal_mul, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    ring

theorem meas_of_sec (X : Data E r) {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (hP : X.IsSec la P)
    (h0 : ∀ x ∉ X.dom, P x = 0) : Measurable P := by
  classical
  have : P = X.dom.piecewise P fun _ => 0 := by
    funext x
    by_cases hx : x ∈ X.dom
    · rw [Set.piecewise_eq_of_mem _ _ _ hx]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hx, h0 x hx]
  rw [this]
  exact hP.1.continuousOn.measurable_piecewise continuousOn_const (FourierCoefficientDomain.isOpen_dom X).measurableSet

theorem meas_prd (X : Data E r) {la : Wt X.Ψ r} {P Q : Frame X.Ψ r → ℂ} (hP : Measurable P) (hQ : Measurable Q) :
    Measurable (prd X la P Q) := by
  have hn : Measurable (X.nfac la) := by
    unfold Data.nfac
    refine Finset.measurable_prod _ fun τ _ => Finset.measurable_prod _ fun i _ => ?_
    exact (((GlobalTheory.PeterssonCompare.continuous_dmin X τ _).measurable.div
      (GlobalTheory.PeterssonCompare.continuous_dmin X τ _).measurable).norm).pow_const _
  exact (hP.mul (Complex.continuous_conj.measurable.comp hQ)).mul
    (Complex.measurable_ofReal.comp (hn.pow_const 2))

theorem cont_cpt (X : Data E r) (x0 : Frame X.Ψ r) : Continuous (cpt X x0) :=
  ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.cont_cpt X x0

theorem fund_chosen (X : Data E r) : IsOrth X (x0F X) ∧ IsFundSet X (x0F X) (Deg.fundF X) ∧
    Deg.covol X = muF X (x0F X) (Deg.fundF X) := by
  have ho : IsOrth X (x0F X) := fun τ => (X.signature τ).choose_spec.2
  have h := GlobalTheory.MetricWeightTest.exists_fundSet_orth X ho
  unfold Deg.fundF Deg.covol
  rw [dif_pos h, dif_pos h]
  exact ⟨ho, h.choose_spec, rfl⟩

end FD

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r} {W : HSp D}
  {dict : ∀ σ : c.F →+* ℂ, GA D W → Σ k, Frame ((U σ).X k).Ψ D.R.r}

theorem transfer (hL : abelian₂.LevelLaws U W dict) {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) (k : (U σ).Comp) :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ⊤ ∧
      (∀ x0 FF, IsOrth ((U σ).X k) x0 → IsFundSet ((U σ).X k) x0 FF → muF ((U σ).X k) x0 FF ≠ ⊤) ∧
      ∀ Φ : ∀ k, Frame ((U σ).X k).Ψ D.R.r → ℂ, (∀ k, Measurable (Φ k)) →
        (∀ k, ∀ γ ∈ ((U σ).X k).Γ, ∀ x ∈ ((U σ).X k).dom, Φ k (lact γ x) = Φ k x) →
        (∀ k, ∀ b ∈ Bor ((U σ).X k).Ψ D.R.r, ∀ x ∈ ((U σ).X k).dom, Φ k (rmul x b) = Φ k x) →
        Measurable (fun q : AutQ W => Φ (dict σ q.out).1 (dict σ q.out).2) ∧
        ((∀ k', k' ≠ k → ∀ x, Φ k' x = 0) → ∀ x0 FF, IsOrth ((U σ).X k) x0 → IsFundSet ((U σ).X k) x0 FF →
          ∫ q, Φ (dict σ q.out).1 (dict σ q.out).2 ∂(muQ1 W) =
            (C.toReal : ℂ) * ∫ z in FF, Φ k (cpt ((U σ).X k) x0 z) ∂(muF ((U σ).X k) x0)) := by
  obtain ⟨hP, hV⟩ := GlobalTheory.FinalJoin2.volPairEx_and_finVol D W hL.sig
  have hvp := Formalism.L2.Pj.volPair_isVolPair W hP
  haveI : (Formalism.L2.Pj.volPair W).1.IsHaarMeasure := hvp.1.1
  have h0 : (Formalism.L2.Pj.volPair W).1 (Formalism.L2.Pj.volPair W).2 ≠ 0 := Formalism.L2.Pj.muQ_univ W ▸ hV.1
  have h1 : (Formalism.L2.Pj.volPair W).1 (Formalism.L2.Pj.volPair W).2 ≠ ⊤ := Formalism.L2.Pj.muQ_univ W ▸ hV.2
  obtain ⟨Kf, th, hr, hK, hth, hd, hu⟩ := hL.dictU σ hσ
  have hU := hL.unf σ hσ
  have hΨ : ∀ k k', ((U σ).X k).Ψ = ((U σ).X k').Ψ ∧ ((U σ).X k).p0 = ((U σ).X k').p0 := fun k k' =>
    ⟨Finset.ext fun τ => ((hU.2.1 k).2 τ).trans ((hU.2.1 k').2 τ).symm, (hU.2.1 k).1.trans (hU.2.1 k').1.symm⟩
  have hM : 0 < l.M := by have := l.three_le; omega
  obtain ⟨κ, hκ0, hκ1, hI⟩ := GlobalTheory.PeterssonCompare.lintegral_adelic W (U σ).X (dict σ) hM hth hd hK hu hΨ
    _ hvp.2 h0 h1
  obtain ⟨κ2, h20, h21, hH⟩ := GlobalTheory.T.flagQuotientIntegral_eq_universal_const_mul D.R.r ((U σ).X k).p0 ((U σ).X k).Ψ.card
  have hQ := hH D.host.E ((U σ).X k) rfl rfl
  have key : ∀ F : ∀ k, Frame ((U σ).X k).Ψ D.R.r → ℝ≥0∞, (∀ k, Measurable (F k)) →
      (∀ k, ∀ γ ∈ ((U σ).X k).Γ, ∀ x ∈ ((U σ).X k).dom, F k (lact γ x) = F k x) →
      (∀ k, ∀ b ∈ Bor ((U σ).X k).Ψ D.R.r, ∀ x ∈ ((U σ).X k).dom, F k (rmul x b) = F k x) →
      Measurable (fun q : AutQ W => F (dict σ q.out).1 (dict σ q.out).2) ∧
      ∫⁻ q, F (dict σ q.out).1 (dict σ q.out).2 ∂(muQ1 W) =
        ((Formalism.L2.Pj.volPair W).1 (Formalism.L2.Pj.volPair W).2)⁻¹ *
          (κ * ∑ k, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.quotInt ((U σ).X k) (F k)) := by
    intro F hF hΓ hB
    obtain ⟨h2, h3⟩ := hI F hF hΓ hB
    have hout : ∀ g, F (dict σ (Formalism.L2.Pj.autMk W g).out).1 (dict σ (Formalism.L2.Pj.autMk W g).out).2 =
        F (dict σ g).1 (dict σ g).2 := by
      intro g
      have h4 : g * (Formalism.L2.Pj.autMk W g).out⁻¹ ∈ GQ W :=
        QuotientGroup.rightRel_apply.1 (Quotient.mk_out g)
      obtain ⟨γ, hγ, e⟩ := hd.1 _ h4 (Formalism.L2.Pj.autMk W g).out
      rw [inv_mul_cancel_right] at e
      rw [e]
      exact (hΓ _ γ hγ _ (hd.2.2.2.1 _)).symm
    have hq : Measurable fun q : Formalism.L2.Pj.AutQ W => F (dict σ q.out).1 (dict σ q.out).2 := by
      rw [measurable_from_quotient]
      have : ((fun q : Formalism.L2.Pj.AutQ W => F (dict σ q.out).1 (dict σ q.out).2) ∘ Quotient.mk'') =
          fun g => F (dict σ g).1 (dict σ g).2 := funext hout
      rw [this]
      exact h2
    have h5 : ∫⁻ q, F (dict σ q.out).1 (dict σ q.out).2 ∂(Formalism.L2.Pj.muQ W) =
        κ * ∑ k, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.quotInt ((U σ).X k) (F k) := by
      rw [Formalism.L2.Pj.muQ, lintegral_map hq (Formalism.L2.Pj.autMk_measurable W)]
      simp only [hout]
      exact h3
    refine ⟨hq, ?_⟩
    rw [Formalism.L2.Pj.muQ1, if_pos (show Formalism.L2.Pj.muQ W Set.univ ≠ 0 ∧ Formalism.L2.Pj.muQ W Set.univ ≠ ⊤
      from hV), lintegral_smul_measure, h5, Formalism.L2.Pj.muQ_univ, smul_eq_mul]
  have hv0 : ((Formalism.L2.Pj.volPair W).1 (Formalism.L2.Pj.volPair W).2)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 h1
  have hv1 : ((Formalism.L2.Pj.volPair W).1 (Formalism.L2.Pj.volPair W).2)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 h0
  refine ⟨((Formalism.L2.Pj.volPair W).1 (Formalism.L2.Pj.volPair W).2)⁻¹ * (κ * κ2), mul_ne_zero hv0 (mul_ne_zero hκ0 h20),
    ENNReal.mul_ne_top hv1 (ENNReal.mul_ne_top hκ1 h21), fun x0 FF ho hF ht => ?_, fun Φ hΦ hΓ hB => ?_⟩
  · have e1 := (key (fun _ _ => 1) (fun _ => measurable_const) (fun _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl)).2
    have e2 := hQ x0 FF (fun _ => 1) ho hF measurable_const (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    rw [setLIntegral_one, ht, ENNReal.mul_top h20] at e2
    have e3 : ∑ k, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.quotInt ((U σ).X k) (fun _ => 1) = ⊤ :=
      ENNReal.sum_eq_top.2 ⟨k, Finset.mem_univ _, e2⟩
    rw [e3, ENNReal.mul_top hκ0, ENNReal.mul_top hv0, lintegral_one, measure_univ] at e1
    exact ENNReal.one_ne_top e1
  · have kG : ∀ G : ℂ → ℝ≥0∞, Measurable G → _ := fun G hG => key (fun k x => G (Φ k x)) (fun k => hG.comp (hΦ k))
      (fun k γ hγ x hx => by simp only [hΓ k γ hγ x hx]) (fun k b hb x hx => by simp only [hB k b hb x hx])
    have hm : Measurable (fun q : AutQ W => Φ (dict σ q.out).1 (dict σ q.out).2) := by
      intro s hs
      have := (kG (s.indicator 1) (measurable_one.indicator hs)).1 (measurableSet_singleton 1)
      convert this using 1
      ext q
      by_cases hq : Φ (dict σ q.out).1 (dict σ q.out).2 ∈ s <;> simp [hq]
    refine ⟨hm, fun hz x0 FF ho hF => ?_⟩
    refine integral_transfer _ _ _ hm ((hΦ k).comp (cont_cpt _ x0).measurable) fun G hG hG0 => ?_
    rw [(kG G hG).2, Finset.sum_eq_single k (fun k' _ hk' => by
        simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.quotInt, hz k' hk', hG0]) (fun h => absurd (Finset.mem_univ _) h),
      hQ x0 FF (fun x => G (Φ k x)) ho hF (hG.comp (hΦ k)) (fun γ hγ x hx => by simp only [hΓ k γ hγ x hx])
        (fun b hb x hx => by simp only [hB k b hb x hx])]
    simp only [mul_assoc]

theorem transfer_sec (hL : abelian₂.LevelLaws U W dict) {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) (k : (U σ).Comp) :
    ∃ C : ℝ, 0 < C ∧
      (∀ x0 FF, IsOrth ((U σ).X k) x0 → IsFundSet ((U σ).X k) x0 FF → muF ((U σ).X k) x0 FF ≠ ⊤) ∧
      ∀ (la : ∀ k, Wt ((U σ).X k).Ψ D.R.r) (P Q : FDSec (U σ).X), (∀ k, ((U σ).X k).IsSec (la k) (P k)) →
        (∀ k, ((U σ).X k).IsSec (la k) (Q k)) → (∀ k, ∀ x ∉ ((U σ).X k).dom, P k x = 0) →
        (∀ k, ∀ x ∉ ((U σ).X k).dom, Q k x = 0) →
        Measurable (fun q : AutQ W => P (dict σ q.out).1 (dict σ q.out).2 *
          starRingEnd ℂ (Q (dict σ q.out).1 (dict σ q.out).2)) ∧
        ((∀ k', k' ≠ k → ∀ x ∈ ((U σ).X k').dom, P k' x = 0) →
          ∀ x0 FF, IsOrth ((U σ).X k) x0 → IsFundSet ((U σ).X k) x0 FF →
          ∫ q, P (dict σ q.out).1 (dict σ q.out).2 * starRingEnd ℂ (Q (dict σ q.out).1 (dict σ q.out).2) ∂(muQ1 W) =
            (C : ℂ) * ∫ z in FF, prd ((U σ).X k) (la k) (P k) (Q k) (cpt ((U σ).X k) x0 z) ∂(muF ((U σ).X k) x0)) := by
  obtain ⟨C, hC0, hC1, hfin, hT⟩ := transfer hL hσ k
  obtain ⟨Kf, th, hr, hK, hth, hd, hu⟩ := hL.dictU σ hσ
  refine ⟨C.toReal, ENNReal.toReal_pos hC0 hC1, hfin, fun la P Q hP hQ hP0 hQ0 => ?_⟩
  obtain ⟨h1, h2⟩ := hT (fun k => prd ((U σ).X k) (la k) (P k) (Q k))
    (fun k => meas_prd _ (meas_of_sec _ (hP k) (hP0 k)) (meas_of_sec _ (hQ k) (hQ0 k)))
    (fun k γ hγ x hx => prd_eq_of _ _ ((hP k).2.2 γ hγ x hx) ((hQ k).2.2 γ hγ x hx)
      (GlobalTheory.PeterssonCompare.pnorm_lact _ (hP k) hγ hx))
    (fun k b hb x hx => prd_eq_of _ _ ((hP k).2.1 x hx b hb) ((hQ k).2.1 x hx b hb)
      (FrameDegreeData.pnorm_rmul _ _ _ (hP k).2.1 x hx b hb))
  have e : (fun q : AutQ W => prd ((U σ).X (dict σ q.out).1) (la _) (P _) (Q _) (dict σ q.out).2) =
      fun q : AutQ W => P (dict σ q.out).1 (dict σ q.out).2 * starRingEnd ℂ (Q (dict σ q.out).1 (dict σ q.out).2) := by
    funext q
    simp [prd, Data.nfac, hu q.out]
  rw [e] at h1 h2
  refine ⟨h1, fun hz => h2 fun k' hk' x => ?_⟩
  by_cases hx : x ∈ ((U σ).X k').dom
  · simp [prd, hz k' hk' x hx]
  · simp [prd, hP0 k' x hx]

theorem bound_hol (hL : abelian₂.LevelLaws U W dict) {σ : c.F →+* ℂ} (hσ : GoodEmb c σ)
    {la : ∀ k, Wt ((U σ).X k).Ψ D.R.r} {P : FDSec (U σ).X} (hP : P ∈ holSub (U σ).X la) (q : AutQ W) :
    ‖P (dict σ q.out).1 (dict σ q.out).2‖ ≤ (supE (U σ).X la P).toReal := by
  obtain ⟨Kf, th, hr, hK, hth, hD, hu⟩ := hL.dictU σ hσ
  have hfin := supE_ne_top (X := (U σ).X) (la := la) hP
  rw [← pnorm_eq_of_unit ((U σ).X (dict σ q.out).1) (la (dict σ q.out).1)
    (P (dict σ q.out).1) (dict σ q.out).2 (hu q.out), ← ENNReal.ofReal_le_iff_le_toReal hfin]
  exact le_iSup (fun p : FPt (U σ).X => ENNReal.ofReal (((U σ).X p.1).pnorm (la p.1)
    (P p.1) p.2)) ⟨(dict σ q.out).1, ⟨(dict σ q.out).2, hD.2.2.2.1 q.out⟩⟩

theorem hol_of_cuspOn {h : GenFrEx Xo c} {a : WZ D.host.E} {Z : Comp Xo c} {f : Rul Xo c} (hf : f ∈ cuspOn U h a Z)
    {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) : rdU (U σ) f ∈ holSub (U σ).X (Rec.laZ (U σ) a) :=
  (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 (Submodule.mem_inf.1 (Submodule.mem_inf.1 hf).1).2 σ) hσ

theorem ipAll_eq (σ : c.F →+* ℂ) (f g : Rul Xo c) : ipAll U W dict σ f g =
    ∫ q, rdU (U σ) f (dict σ q.out).1 (dict σ q.out).2 *
      starRingEnd ℂ (rdU (U σ) g (dict σ q.out).1 (dict σ q.out).2) ∂(muQ1 W) := by
  unfold ipAll
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  show (1 * rdU (U σ) f (dict σ q.out).1 (dict σ q.out).2) *
    starRingEnd ℂ (1 * rdU (U σ) g (dict σ q.out).1 (dict σ q.out).2) = _
  rw [one_mul, one_mul]

end PetTie

open PetTie in

theorem pet_tie : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c) (W : HSp D) (dict : ∀ σ : c.F →+* ℂ, GA D W → Σ k, Frame ((U σ).X k).Ψ D.R.r), CompLaws U h e → abelian₂.LevelLaws U W dict → FinVol W → ∀ σ, GoodEmb c σ → ∀ Z k, Over (U σ) (e Z) k → ∀ (a : WZ D.host.E) (x0 : Frame ((U σ).X k).Ψ D.R.r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (nd ((U σ).X k)))), IsOrth ((U σ).X k) x0 → IsFundSet ((U σ).X k) x0 FF → (0 < muF ((U σ).X k) x0 FF ∧ muF ((U σ).X k) x0 FF < ⊤) ∧ (∀ f ∈ cuspOn U h a Z, ∀ g ∈ cuspOn U h a Z, ipOn U W dict (xiR D) a (e Z) σ f g = ((lieFacZ Dw (xiR D) a ^ 2 : ℝ) : ℂ) * Deg.pet ((U σ).X k) (laZ (U σ) a k) (rdU (U σ) f k) (rdU (U σ) g k)) ∧ ∀ (m : ℕ) (as : Fin m → ℂ) (fs : Fin m → Rul Xo c), (∀ j, fs j ∈ cuspOn U h a Z) → (∑ j, ∑ j', as j * starRingEnd ℂ (as j') * ipOn U W dict (xiR D) a (e Z) σ (fs j) (fs j')).re = lieFacZ Dw (xiR D) a ^ 2 * ThA.nrm2 ((U σ).X k) x0 FF (laZ (U σ) a k) (fun y => ∑ j, as j * rdU (U σ) (fs j) k y) := by
  intro D H Dw l Xo c U h e W dict L hL _ σ hσ Z k hov a x0 FF ho hF
  obtain ⟨C, hC, hfin, hT⟩ := transfer_sec hL hσ k
  obtain ⟨κ, h1, h2⟩ := comp_over _ H Dw l Xo c _ U h e L σ hσ
  have hk : k = κ Z := (h1 Z k).1 hov
  have off : ∀ (f : Rul Xo c) k', ∀ x ∉ ((U σ).X k').dom, rdU (U σ) f k' x = 0 := fun f k' x hx => dif_neg hx
  have hsec : ∀ f ∈ cuspOn U h a Z, ∀ k', ((U σ).X k').IsSec (Rec.laZ (U σ) a k') (rdU (U σ) f k') :=
    fun f hf => GlobalTheory.PeterssonCompare.isSec_of_mem_holSub _ _ (hol_of_cuspOn hf hσ)
  have hon : ∀ f g, ipOn U W dict (xiR D) a (e Z) σ f g =
      ((lieFacZ Dw (xiR D) a ^ 2 : ℝ) : ℂ) * ipAll U W dict σ f g / ipAll U W dict σ (e Z) (e Z) := by
    intro f g
    have hg : goodOf c σ = σ := if_pos hσ
    simp only [ipOn, if_pos hσ, hg]
  have hee : ∀ x1 F1, IsOrth ((U σ).X k) x1 → IsFundSet ((U σ).X k) x1 F1 →
      ipAll U W dict σ (e Z) (e Z) = (C : ℂ) * ((muF ((U σ).X k) x1 F1).toReal : ℂ) := by
    intro x1 F1 ho1 hF1
    have hs := (L.unf σ hσ).2.2.2.2.1 0 0 CompOver.dom_zero _ (L.e_sec Z)
    rw [ipAll_eq, (hT _ _ _ hs hs (off _) (off _)).2 (fun k' hk' x hx => (h2 Z k' (hk ▸ hk') x hx).1) x1 F1 ho1 hF1]
    congr 1
    rw [setIntegral_congr_fun hF1.1 (g := fun _ => (1 : ℂ)) fun z hz => by
      simp [prd, hov _ (hF1.2.1 hz), Data.nfac, laU]]
    simp [Measure.real]
  have hC' : (C : ℂ) ≠ 0 := by exact_mod_cast hC.ne'
  refine ⟨⟨pos_iff_ne_zero.2 (GlobalTheory.MetricWeightTest.fundSet_pos _ ho hF), (hfin x0 FF ho hF).lt_top⟩,
    fun f hf g hg => ?_, fun m as fs hfs => ?_⟩
  · obtain ⟨o1, o2, o3⟩ := fund_chosen ((U σ).X k)
    rw [hon, hee _ _ o1 o2, ipAll_eq, (hT _ _ _ (hsec f hf) (hsec g hg) (off _) (off _)).2
      (fun k' hk' x hx => (h2 Z k' (hk ▸ hk') x hx).2 a f hf) _ _ o1 o2, Deg.pet, o3, mul_div_assoc,
      mul_div_mul_left _ _ hC']
    rfl
  · have hmem : (∑ j, as j • rdU (U σ) (fs j)) ∈ holSub (U σ).X (Rec.laZ (U σ) a) :=
      Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hol_of_cuspOn (hfs j) hσ)
    have hS := GlobalTheory.PeterssonCompare.isSec_of_mem_holSub _ _ hmem
    have hap : ∀ k' y, (∑ j, as j • rdU (U σ) (fs j)) k' y = ∑ j, as j * rdU (U σ) (fs j) k' y := fun k' y => by
      simp [Finset.sum_apply]
    have hS0 : ∀ k', ∀ x ∉ ((U σ).X k').dom, (∑ j, as j • rdU (U σ) (fs j)) k' x = 0 := fun k' x hx => by
      simp [hap, off _ k' x hx]
    have e1 := (hT _ _ _ hS hS hS0 hS0).2 (fun k' hk' x hx => by
      rw [hap]
      exact Finset.sum_eq_zero fun j _ => by rw [(h2 Z k' (hk ▸ hk') x hx).2 a _ (hfs j), mul_zero]) x0 FF ho hF
    have hint : ∀ j j', Integrable (fun q : AutQ W => rdU (U σ) (fs j) (dict σ q.out).1 (dict σ q.out).2 *
        starRingEnd ℂ (rdU (U σ) (fs j') (dict σ q.out).1 (dict σ q.out).2)) (muQ1 W) := fun j j' =>
      Integrable.of_bound (hT _ _ _ (hsec _ (hfs j)) (hsec _ (hfs j')) (off _) (off _)).1.aestronglyMeasurable _
        (Filter.Eventually.of_forall fun q => by
          rw [norm_mul, Complex.norm_conj]
          exact mul_le_mul (bound_hol hL hσ (hol_of_cuspOn (hfs j) hσ) q)
            (bound_hol hL hσ (hol_of_cuspOn (hfs j') hσ) q) (norm_nonneg _) ENNReal.toReal_nonneg)
    have e2 : ∑ j, ∑ j', as j * starRingEnd ℂ (as j') * ipAll U W dict σ (fs j) (fs j') =
        ∫ q, (∑ j, as j • rdU (U σ) (fs j)) (dict σ q.out).1 (dict σ q.out).2 *
          starRingEnd ℂ ((∑ j, as j • rdU (U σ) (fs j)) (dict σ q.out).1 (dict σ q.out).2) ∂(muQ1 W) := by
      simp only [ipAll_eq, ← integral_const_mul]
      rw [Finset.sum_congr rfl fun j _ =>
        (integral_finset_sum _ fun j' _ => (hint j j').const_mul (as j * starRingEnd ℂ (as j'))).symm,
        ← integral_finset_sum _ fun j _ => integrable_finset_sum _ fun j' _ =>
          (hint j j').const_mul (as j * starRingEnd ℂ (as j'))]
      refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
      simp only [hap, map_sum, map_mul, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by ring
    have e3 : ∀ z, prd ((U σ).X k) (Rec.laZ (U σ) a k) ((∑ j, as j • rdU (U σ) (fs j)) k)
        ((∑ j, as j • rdU (U σ) (fs j)) k) z =
        ((((U σ).X k).pnorm (Rec.laZ (U σ) a k) (fun y => ∑ j, as j * rdU (U σ) (fs j) k y) z ^ 2 : ℝ) : ℂ) := by
      intro z
      show _ = (((‖∑ j, as j * rdU (U σ) (fs j) k z‖ * ((U σ).X k).nfac (Rec.laZ (U σ) a k) z) ^ 2 : ℝ) : ℂ)
      rw [prd, hap, Complex.mul_conj, Complex.normSq_eq_norm_sq, mul_pow, Complex.ofReal_mul]
    simp only [e3] at e1
    rw [integral_complex_ofReal, ← e2] at e1
    have e4 : ∑ j, ∑ j', as j * starRingEnd ℂ (as j') * ipOn U W dict (xiR D) a (e Z) σ (fs j) (fs j') =
        ((lieFacZ Dw (xiR D) a ^ 2 : ℝ) : ℂ) * (∑ j, ∑ j', as j * starRingEnd ℂ (as j') *
          ipAll U W dict σ (fs j) (fs j')) / ipAll U W dict σ (e Z) (e Z) := by
      simp only [hon, Finset.mul_sum, Finset.sum_div]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by ring
    rw [e4, e1, hee _ _ ho hF, mul_div_assoc, mul_div_mul_left _ _ hC', ← Complex.ofReal_div, ← Complex.ofReal_mul,
      Complex.ofReal_re]
    rfl

end PositivityTheory.Xgy
